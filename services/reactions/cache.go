package main

import (
	"context"
	"sync"
	"time"
)

const reactionCacheTTL = 30 * time.Second

type cachedReactionPage struct {
	result     reactionPageResult
	expires    time.Time
	generation uint64
}

type cachedViewerReviews struct {
	result     map[string]reviewEvent
	expires    time.Time
	generation uint64
}

type reactionPageLoad struct {
	done       chan struct{}
	result     reactionPageResult
	err        error
	generation uint64
}

type viewerReviewsLoad struct {
	done       chan struct{}
	result     map[string]reviewEvent
	err        error
	generation uint64
}

type reactionCache struct {
	mu                sync.Mutex
	lastSweep         time.Time
	pages             map[string]cachedReactionPage
	pageLoads         map[string]*reactionPageLoad
	pageGenerations   map[string]uint64
	viewers           map[string]cachedViewerReviews
	viewerLoads       map[string]*viewerReviewsLoad
	viewerGenerations map[string]uint64
}

func (c *reactionCache) sweepExpired(now time.Time) {
	if !c.lastSweep.IsZero() && now.Sub(c.lastSweep) < reactionCacheTTL {
		return
	}
	for key, cached := range c.pages {
		if !now.Before(cached.expires) {
			delete(c.pages, key)
		}
	}
	for key, cached := range c.viewers {
		if !now.Before(cached.expires) {
			delete(c.viewers, key)
		}
	}
	c.lastSweep = now
}

func (c *reactionCache) page(ctx context.Context, key string, load func() (reactionPageResult, error)) (reactionPageResult, error) {
	c.mu.Lock()
	if c.pages == nil {
		c.pages = make(map[string]cachedReactionPage)
		c.pageLoads = make(map[string]*reactionPageLoad)
		c.pageGenerations = make(map[string]uint64)
	}
	now := time.Now()
	c.sweepExpired(now)
	generation := c.pageGenerations[key]
	if cached, ok := c.pages[key]; ok && cached.generation == generation && now.Before(cached.expires) {
		c.mu.Unlock()
		return cached.result, nil
	}
	if pending, ok := c.pageLoads[key]; ok && pending.generation == generation {
		c.mu.Unlock()
		select {
		case <-pending.done:
			return pending.result, pending.err
		case <-ctx.Done():
			return reactionPageResult{}, ctx.Err()
		}
	}
	pending := &reactionPageLoad{done: make(chan struct{}), generation: generation}
	c.pageLoads[key] = pending
	c.mu.Unlock()

	pending.result, pending.err = load()
	c.mu.Lock()
	if pending.err == nil && c.pageGenerations[key] == generation {
		c.pages[key] = cachedReactionPage{result: pending.result, expires: time.Now().Add(reactionCacheTTL), generation: generation}
	}
	if c.pageLoads[key] == pending {
		delete(c.pageLoads, key)
	}
	close(pending.done)
	c.mu.Unlock()
	return pending.result, pending.err
}

func (c *reactionCache) viewer(ctx context.Context, key string, load func() (map[string]reviewEvent, error)) (map[string]reviewEvent, error) {
	c.mu.Lock()
	if c.viewers == nil {
		c.viewers = make(map[string]cachedViewerReviews)
		c.viewerLoads = make(map[string]*viewerReviewsLoad)
		c.viewerGenerations = make(map[string]uint64)
	}
	now := time.Now()
	c.sweepExpired(now)
	generation := c.viewerGenerations[key]
	if cached, ok := c.viewers[key]; ok && cached.generation == generation && now.Before(cached.expires) {
		c.mu.Unlock()
		return cached.result, nil
	}
	if pending, ok := c.viewerLoads[key]; ok && pending.generation == generation {
		c.mu.Unlock()
		select {
		case <-pending.done:
			return pending.result, pending.err
		case <-ctx.Done():
			return nil, ctx.Err()
		}
	}
	pending := &viewerReviewsLoad{done: make(chan struct{}), generation: generation}
	c.viewerLoads[key] = pending
	c.mu.Unlock()

	pending.result, pending.err = load()
	c.mu.Lock()
	if pending.err == nil && c.viewerGenerations[key] == generation {
		c.viewers[key] = cachedViewerReviews{result: pending.result, expires: time.Now().Add(reactionCacheTTL), generation: generation}
	}
	if c.viewerLoads[key] == pending {
		delete(c.viewerLoads, key)
	}
	close(pending.done)
	c.mu.Unlock()
	return pending.result, pending.err
}

func (c *reactionCache) invalidate(pageURL, remarkID string) {
	c.mu.Lock()
	defer c.mu.Unlock()
	if pageURL != "" {
		if c.pageGenerations == nil {
			c.pageGenerations = make(map[string]uint64)
		}
		delete(c.pages, pageURL)
		c.pageGenerations[pageURL]++
	}
	if remarkID != "" {
		if c.viewerGenerations == nil {
			c.viewerGenerations = make(map[string]uint64)
		}
		delete(c.viewers, remarkID)
		c.viewerGenerations[remarkID]++
	}
}
