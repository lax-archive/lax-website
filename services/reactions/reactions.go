package main

import (
	"bytes"
	"context"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"net/http"
	"net/url"
	"sort"
	"strconv"
	"strings"
	"time"
	"unicode/utf8"
)

const (
	reviewEndorse        = "endorse"
	reviewFlag           = "flag"
	reviewClear          = "clear"
	reviewPrefix         = "lax-review:v2:"
	endorseMarker        = "✅ Endorsed\n\n" + reviewPrefix + reviewEndorse
	clearMarker          = "↩️ Review cleared\n\n" + reviewPrefix + reviewClear
	maximumFlagTextBytes = 2000
	maximumFlagLine      = 1_000_000
)

var publicReviews = []string{reviewEndorse, reviewFlag}

type reviewEvent struct {
	Kind      string
	Message   string
	LineStart int
	LineEnd   int
}

type publicFlag struct {
	ID        string     `json:"id"`
	Message   string     `json:"message"`
	LineStart int        `json:"line_start,omitempty"`
	LineEnd   int        `json:"line_end,omitempty"`
	Author    namedVoter `json:"author"`
	Time      time.Time  `json:"time"`
}

type reactionPageResult struct {
	URL              string                  `json:"url"`
	Counts           map[string]int          `json:"counts"`
	Voters           map[string][]namedVoter `json:"voters"`
	Flags            []publicFlag            `json:"flags"`
	viewerByRemarkID map[string]reviewEvent  `json:"-"`
}

type remarkReactionComment struct {
	ID       string    `json:"id"`
	ParentID string    `json:"pid"`
	Orig     string    `json:"orig"`
	Deleted  bool      `json:"delete"`
	Time     time.Time `json:"time"`
	User     struct {
		ID string `json:"id"`
	} `json:"user"`
}

type remarkFindResponse struct {
	Comments []remarkReactionComment `json:"comments"`
}

func validReview(value string) bool {
	return value == reviewEndorse || value == reviewFlag || value == reviewClear
}

func hiddenReactionURL(pageURL string) (string, error) {
	canonical, err := canonicalPage(pageURL)
	if err != nil {
		return "", err
	}
	parsed, err := url.Parse(canonical)
	if err != nil {
		return "", err
	}
	parsed.Path = "/_reactions" + parsed.Path
	return parsed.String(), nil
}

func normalizeFlagMessage(value string) (string, error) {
	value = strings.TrimSpace(strings.ReplaceAll(value, "\r\n", "\n"))
	if value == "" {
		return "", errors.New("a flag explanation is required")
	}
	if !utf8.ValidString(value) || len(value) > maximumFlagTextBytes || strings.ContainsRune(value, '\x00') {
		return "", fmt.Errorf("flag explanation must be valid text no longer than %d bytes", maximumFlagTextBytes)
	}
	return value, nil
}

func validateLineReference(start, end int) error {
	if start == 0 && end == 0 {
		return nil
	}
	if start < 1 || end != start || end > maximumFlagLine {
		return errors.New("flag source annotation must reference exactly one line")
	}
	return nil
}

func reviewMarker(event reviewEvent) (string, error) {
	switch event.Kind {
	case reviewEndorse:
		return endorseMarker, nil
	case reviewClear:
		return clearMarker, nil
	case reviewFlag:
		message, err := normalizeFlagMessage(event.Message)
		if err != nil {
			return "", err
		}
		if err = validateLineReference(event.LineStart, event.LineEnd); err != nil {
			return "", err
		}
		return fmt.Sprintf("🚩 %s\n\n%s%s:%d:%d", message, reviewPrefix, reviewFlag, event.LineStart, event.LineEnd), nil
	default:
		return "", errors.New("invalid review event")
	}
}

func reviewFromMarker(value string) (reviewEvent, bool) {
	value = strings.TrimSpace(strings.ReplaceAll(value, "\r\n", "\n"))
	if value == endorseMarker {
		return reviewEvent{Kind: reviewEndorse}, true
	}
	if value == clearMarker {
		return reviewEvent{Kind: reviewClear}, true
	}
	lastBreak := strings.LastIndex(value, "\n")
	if lastBreak < 0 || !strings.HasPrefix(value, "🚩 ") {
		return reviewEvent{}, false
	}
	metadata := strings.TrimSpace(value[lastBreak+1:])
	metadataPrefix := reviewPrefix + reviewFlag + ":"
	if !strings.HasPrefix(metadata, metadataPrefix) {
		return reviewEvent{}, false
	}
	rangeParts := strings.Split(strings.TrimPrefix(metadata, metadataPrefix), ":")
	if len(rangeParts) != 2 {
		return reviewEvent{}, false
	}
	start, startErr := strconv.Atoi(rangeParts[0])
	end, endErr := strconv.Atoi(rangeParts[1])
	if startErr != nil || endErr != nil || validateLineReference(start, end) != nil {
		return reviewEvent{}, false
	}
	body := strings.TrimSpace(value[:lastBreak])
	message, err := normalizeFlagMessage(strings.TrimSpace(strings.TrimPrefix(body, "🚩")))
	if err != nil {
		return reviewEvent{}, false
	}
	return reviewEvent{Kind: reviewFlag, Message: message, LineStart: start, LineEnd: end}, true
}

func (a *app) reactionPage(ctx context.Context, pageURL string) (reactionPageResult, error) {
	hiddenURL, err := hiddenReactionURL(pageURL)
	if err != nil {
		return reactionPageResult{}, err
	}
	endpoint, err := url.Parse(a.config.remarkFindURL)
	if err != nil {
		return reactionPageResult{}, err
	}
	query := endpoint.Query()
	query.Set("site", "remark")
	query.Set("url", hiddenURL)
	query.Set("sort", "+time")
	query.Set("format", "plain")
	endpoint.RawQuery = query.Encode()
	request, err := http.NewRequestWithContext(ctx, http.MethodGet, endpoint.String(), nil)
	if err != nil {
		return reactionPageResult{}, err
	}
	request.Header.Set("Accept", "application/json")
	upstream, err := a.client.Do(request)
	if err != nil {
		return reactionPageResult{}, err
	}
	defer upstream.Body.Close()
	if upstream.StatusCode != http.StatusOK {
		return reactionPageResult{}, fmt.Errorf("Remark42 find endpoint returned %d", upstream.StatusCode)
	}
	var found remarkFindResponse
	if err = json.NewDecoder(io.LimitReader(upstream.Body, 8<<20)).Decode(&found); err != nil {
		return reactionPageResult{}, err
	}

	latest := make(map[string]remarkReactionComment)
	for _, comment := range found.Comments {
		_, marker := reviewFromMarker(comment.Orig)
		if comment.Deleted || comment.ParentID != "" || !marker || !remarkIDPattern.MatchString(comment.User.ID) {
			continue
		}
		previous, exists := latest[comment.User.ID]
		if !exists || comment.Time.After(previous.Time) || (comment.Time.Equal(previous.Time) && comment.ID > previous.ID) {
			latest[comment.User.ID] = comment
		}
	}

	result := reactionPageResult{
		URL:              pageURL,
		Counts:           map[string]int{reviewEndorse: 0, reviewFlag: 0},
		Voters:           map[string][]namedVoter{reviewEndorse: {}, reviewFlag: {}},
		Flags:            []publicFlag{},
		viewerByRemarkID: make(map[string]reviewEvent),
	}
	for remarkID, comment := range latest {
		review, _ := reviewFromMarker(comment.Orig)
		if review.Kind == reviewClear {
			continue
		}
		person, present, lookupErr := a.store.identity(remarkID)
		if lookupErr != nil {
			return reactionPageResult{}, lookupErr
		}
		if !present || strings.TrimSpace(person.Name) == "" || !validORCID(person.ORCID) {
			continue
		}
		author := namedVoter{Name: person.Name, ORCID: person.ORCID}
		result.viewerByRemarkID[remarkID] = review
		result.Counts[review.Kind]++
		result.Voters[review.Kind] = append(result.Voters[review.Kind], author)
		if review.Kind == reviewFlag {
			result.Flags = append(result.Flags, publicFlag{ID: comment.ID, Message: review.Message, LineStart: review.LineStart, LineEnd: review.LineEnd, Author: author, Time: comment.Time})
		}
	}
	for _, review := range publicReviews {
		sort.Slice(result.Voters[review], func(i, j int) bool {
			left, right := strings.ToLower(result.Voters[review][i].Name), strings.ToLower(result.Voters[review][j].Name)
			if left == right {
				return result.Voters[review][i].ORCID < result.Voters[review][j].ORCID
			}
			return left < right
		})
	}
	sort.Slice(result.Flags, func(i, j int) bool {
		if result.Flags[i].Time.Equal(result.Flags[j].Time) {
			return result.Flags[i].ID > result.Flags[j].ID
		}
		return result.Flags[i].Time.After(result.Flags[j].Time)
	})
	return result, nil
}

func (a *app) appendReview(r *http.Request, pageURL string, event reviewEvent) error {
	if strings.HasSuffix(pageURL, "/") && (event.LineStart != 0 || event.LineEnd != 0) {
		return errors.New("submission flags cannot reference concept source lines")
	}
	marker, err := reviewMarker(event)
	if err != nil {
		return err
	}
	hiddenURL, err := hiddenReactionURL(pageURL)
	if err != nil {
		return err
	}
	payload := struct {
		Text    string `json:"text"`
		Title   string `json:"title"`
		Locator struct {
			Site string `json:"site"`
			URL  string `json:"url"`
		} `json:"locator"`
	}{Text: marker, Title: "Lax Archive review"}
	payload.Locator.Site = "remark"
	payload.Locator.URL = hiddenURL
	body, err := json.Marshal(payload)
	if err != nil {
		return err
	}
	request, err := http.NewRequestWithContext(r.Context(), http.MethodPost, a.config.remarkPostURL, bytes.NewReader(body))
	if err != nil {
		return err
	}
	request.Header.Set("Cookie", r.Header.Get("Cookie"))
	request.Header.Set("Accept", "application/json")
	request.Header.Set("Content-Type", "application/json")
	if xsrf, cookieErr := r.Cookie("XSRF-TOKEN"); cookieErr == nil && xsrf.Value != "" {
		request.Header.Set("X-XSRF-TOKEN", xsrf.Value)
	} else {
		return errors.New("Remark42 XSRF cookie is missing")
	}
	if address := clientIP(r); address != "" {
		request.Header.Set("X-Forwarded-For", address)
		request.Header.Set("X-Real-IP", address)
	}
	upstream, err := a.client.Do(request)
	if err != nil {
		return err
	}
	defer upstream.Body.Close()
	if upstream.StatusCode != http.StatusCreated && upstream.StatusCode != http.StatusOK {
		message, _ := io.ReadAll(io.LimitReader(upstream.Body, 8<<10))
		return fmt.Errorf("Remark42 comment endpoint returned %d: %s", upstream.StatusCode, strings.TrimSpace(string(message)))
	}
	return nil
}
