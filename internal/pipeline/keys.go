package pipeline

import (
	"crypto/sha256"
	"encoding/hex"
	"sort"
	"strconv"
	"strings"
)

type CacheParts struct {
	QueryHash           string
	CorpusHash          string
	ModelID             string
	TokenizerVersion    string
	TokenizerVocabHash  string
	WeightsHash         string
	ConceptDFVersion    string
	MaxTokens           int
	MaxDocuments        int
	ObjectiveStyle      string
}

func BuildCacheKey(p CacheParts) string {
	parts := []string{
		"q=" + p.QueryHash,
		"c=" + p.CorpusHash,
		"m=" + p.ModelID,
		"tokv=" + p.TokenizerVersion,
		"vocab=" + p.TokenizerVocabHash,
		"w=" + p.WeightsHash,
		"dfv=" + p.ConceptDFVersion,
		"B=" + strconv.Itoa(p.MaxTokens),
		"D=" + strconv.Itoa(p.MaxDocuments),
		"obj=" + p.ObjectiveStyle,
	}
	sort.Strings(parts)
	h := sha256.Sum256([]byte(strings.Join(parts, "|")))
	return "sha256:" + hex.EncodeToString(h[:])
}
