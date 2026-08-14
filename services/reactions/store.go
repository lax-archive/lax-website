package main

import (
	"bytes"
	"encoding/json"
	"errors"
	"fmt"
	"os"
	"path/filepath"
	"sort"
	"strings"
	"time"

	bolt "go.etcd.io/bbolt"
)

var (
	identityBucket = []byte("identities")
	votesBucket    = []byte("votes")
)

type identity struct {
	RemarkID string    `json:"-"`
	ORCID    string    `json:"orcid"`
	Name     string    `json:"name"`
	Updated  time.Time `json:"updated"`
}

type namedVoter struct {
	Name  string `json:"name"`
	ORCID string `json:"orcid"`
}

type pageResult struct {
	URL      string                  `json:"url"`
	Likes    int                     `json:"likes"`
	Dislikes int                     `json:"dislikes"`
	Voters   map[string][]namedVoter `json:"voters"`
}

type store struct{ db *bolt.DB }

func openStore(path string) (*store, error) {
	if err := os.MkdirAll(filepath.Dir(path), 0o700); err != nil {
		return nil, fmt.Errorf("create data directory: %w", err)
	}
	db, err := bolt.Open(path, 0o600, &bolt.Options{Timeout: 5 * time.Second})
	if err != nil {
		return nil, fmt.Errorf("open database: %w", err)
	}
	if err = db.Update(func(tx *bolt.Tx) error {
		if _, e := tx.CreateBucketIfNotExists(identityBucket); e != nil {
			return e
		}
		_, e := tx.CreateBucketIfNotExists(votesBucket)
		return e
	}); err != nil {
		db.Close()
		return nil, fmt.Errorf("initialize database: %w", err)
	}
	return &store{db: db}, nil
}

func (s *store) close() error { return s.db.Close() }

func (s *store) putIdentity(value identity) error {
	if value.RemarkID == "" || value.ORCID == "" || strings.TrimSpace(value.Name) == "" {
		return errors.New("identity is incomplete")
	}
	data, err := json.Marshal(value)
	if err != nil {
		return err
	}
	return s.db.Update(func(tx *bolt.Tx) error {
		return tx.Bucket(identityBucket).Put([]byte(value.RemarkID), data)
	})
}

func identityFromBucket(bucket *bolt.Bucket, remarkID string) (identity, bool, error) {
	data := bucket.Get([]byte(remarkID))
	if data == nil {
		return identity{}, false, nil
	}
	var value identity
	if err := json.Unmarshal(data, &value); err != nil {
		return identity{}, false, err
	}
	value.RemarkID = remarkID
	return value, true, nil
}

func (s *store) identity(remarkID string) (identity, bool, error) {
	var value identity
	var found bool
	err := s.db.View(func(tx *bolt.Tx) (err error) {
		value, found, err = identityFromBucket(tx.Bucket(identityBucket), remarkID)
		return err
	})
	return value, found, err
}

func (s *store) identities(remarkIDs []string) ([]identity, error) {
	result := make([]identity, 0, len(remarkIDs))
	err := s.db.View(func(tx *bolt.Tx) error {
		bucket := tx.Bucket(identityBucket)
		for _, remarkID := range remarkIDs {
			value, found, err := identityFromBucket(bucket, remarkID)
			if err != nil {
				return err
			}
			if found && strings.TrimSpace(value.Name) != "" {
				result = append(result, value)
			}
		}
		return nil
	})
	return result, err
}

func voteKey(pageURL, remarkID string) []byte {
	return []byte(pageURL + "\x00" + remarkID)
}

func (s *store) setVote(pageURL, remarkID string, vote int) error {
	return s.db.Update(func(tx *bolt.Tx) error {
		bucket := tx.Bucket(votesBucket)
		key := voteKey(pageURL, remarkID)
		if vote == 0 {
			return bucket.Delete(key)
		}
		if vote != -1 && vote != 1 {
			return errors.New("invalid vote")
		}
		return bucket.Put(key, []byte{byte(vote + 1)})
	})
}

func (s *store) page(pageURL string) (pageResult, error) {
	result := pageResult{URL: pageURL, Voters: map[string][]namedVoter{"likes": {}, "dislikes": {}}}
	prefix := []byte(pageURL + "\x00")
	err := s.db.View(func(tx *bolt.Tx) error {
		votes := tx.Bucket(votesBucket)
		identities := tx.Bucket(identityBucket)
		cursor := votes.Cursor()
		for key, rawVote := cursor.Seek(prefix); key != nil && bytes.HasPrefix(key, prefix); key, rawVote = cursor.Next() {
			if len(rawVote) != 1 {
				continue
			}
			remarkID := string(key[len(prefix):])
			person, found, err := identityFromBucket(identities, remarkID)
			if err != nil {
				return err
			}
			if !found || strings.TrimSpace(person.Name) == "" {
				continue
			}
			voter := namedVoter{Name: person.Name, ORCID: person.ORCID}
			switch int(rawVote[0]) - 1 {
			case 1:
				result.Likes++
				result.Voters["likes"] = append(result.Voters["likes"], voter)
			case -1:
				result.Dislikes++
				result.Voters["dislikes"] = append(result.Voters["dislikes"], voter)
			}
		}
		return nil
	})
	for _, voters := range result.Voters {
		sort.Slice(voters, func(i, j int) bool {
			left, right := strings.ToLower(voters[i].Name), strings.ToLower(voters[j].Name)
			if left == right {
				return voters[i].ORCID < voters[j].ORCID
			}
			return left < right
		})
	}
	return result, err
}

func (s *store) viewerVote(pageURL, remarkID string) (int, error) {
	vote := 0
	err := s.db.View(func(tx *bolt.Tx) error {
		raw := tx.Bucket(votesBucket).Get(voteKey(pageURL, remarkID))
		if len(raw) == 1 {
			vote = int(raw[0]) - 1
		}
		return nil
	})
	return vote, err
}

func (s *store) backup(dir string, keep int) error {
	if err := os.MkdirAll(dir, 0o700); err != nil {
		return err
	}
	path := filepath.Join(dir, "reactions-"+time.Now().UTC().Format("20060102-150405")+".db")
	if err := s.db.View(func(tx *bolt.Tx) error { return tx.CopyFile(path, 0o600) }); err != nil {
		return err
	}
	files, err := filepath.Glob(filepath.Join(dir, "reactions-*.db"))
	if err != nil {
		return err
	}
	sort.Strings(files)
	for len(files) > keep {
		if err = os.Remove(files[0]); err != nil {
			return err
		}
		files = files[1:]
	}
	return nil
}
