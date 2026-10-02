package main

import (
	"context"
	"sync"
	"sync/atomic"
	"testing"
)

func TestReactionCacheCoalescesConcurrentPageLoads(t *testing.T) {
	var cache reactionCache
	var calls atomic.Int32
	var started sync.Once
	loadStarted := make(chan struct{})
	releaseLoad := make(chan struct{})
	load := func() (reactionPageResult, error) {
		calls.Add(1)
		started.Do(func() { close(loadStarted) })
		<-releaseLoad
		return reactionPageResult{URL: "https://laxarchive.org/Lax2/"}, nil
	}

	results := make(chan reactionPageResult, 2)
	errors := make(chan error, 2)
	for range 2 {
		go func() {
			result, err := cache.page(context.Background(), "https://laxarchive.org/Lax2/", load)
			results <- result
			errors <- err
		}()
	}
	<-loadStarted
	close(releaseLoad)
	for range 2 {
		if err := <-errors; err != nil {
			t.Fatal(err)
		}
		if result := <-results; result.URL != "https://laxarchive.org/Lax2/" {
			t.Fatalf("unexpected cached result: %+v", result)
		}
	}
	if calls.Load() != 1 {
		t.Fatalf("concurrent cache miss ran %d loaders; want one", calls.Load())
	}
}
