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
	"strings"
	"time"
)

const (
	reactionLike    = "like"
	reactionDislike = "dislike"
	reactionRocket  = "rocket"
	reactionClear   = "clear"
	reactionPrefix  = "lax-reaction:v1:"
)

var publicReactions = []string{reactionLike, reactionDislike, reactionRocket}

type reactionPageResult struct {
	URL              string                  `json:"url"`
	Counts           map[string]int          `json:"counts"`
	Voters           map[string][]namedVoter `json:"voters"`
	viewerByRemarkID map[string]string       `json:"-"`
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

func validReaction(value string) bool {
	return value == reactionLike || value == reactionDislike || value == reactionRocket
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

func reactionFromMarker(value string) (string, bool) {
	value = strings.TrimSpace(value)
	if !strings.HasPrefix(value, reactionPrefix) {
		return "", false
	}
	reaction := strings.TrimPrefix(value, reactionPrefix)
	return reaction, validReaction(reaction) || reaction == reactionClear
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
		_, marker := reactionFromMarker(comment.Orig)
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
		Counts:           map[string]int{reactionLike: 0, reactionDislike: 0, reactionRocket: 0},
		Voters:           map[string][]namedVoter{reactionLike: {}, reactionDislike: {}, reactionRocket: {}},
		viewerByRemarkID: make(map[string]string),
	}
	for remarkID, comment := range latest {
		reaction, _ := reactionFromMarker(comment.Orig)
		if reaction == reactionClear {
			continue
		}
		person, present, lookupErr := a.store.identity(remarkID)
		if lookupErr != nil {
			return reactionPageResult{}, lookupErr
		}
		if !present || strings.TrimSpace(person.Name) == "" || !validORCID(person.ORCID) {
			continue
		}
		result.viewerByRemarkID[remarkID] = reaction
		result.Counts[reaction]++
		result.Voters[reaction] = append(result.Voters[reaction], namedVoter{Name: person.Name, ORCID: person.ORCID})
	}
	for _, reaction := range publicReactions {
		sort.Slice(result.Voters[reaction], func(i, j int) bool {
			left, right := strings.ToLower(result.Voters[reaction][i].Name), strings.ToLower(result.Voters[reaction][j].Name)
			if left == right {
				return result.Voters[reaction][i].ORCID < result.Voters[reaction][j].ORCID
			}
			return left < right
		})
	}
	return result, nil
}

func (a *app) appendReaction(r *http.Request, pageURL, reaction string) error {
	if !validReaction(reaction) && reaction != reactionClear {
		return errors.New("invalid reaction event")
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
	}{Text: reactionPrefix + reaction, Title: "Lax Archive reaction"}
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
