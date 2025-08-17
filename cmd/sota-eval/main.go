// SOTA Evaluation CLI - Comprehensive evaluation harness for ContextLite
// against state-of-the-art RAG systems including BM25, embedding-based, and LLM reranking.

package main

import (
	"context"
	"flag"
	"fmt"
	"log"
	"time"

	"contextlite/internal/evaluation"
)

func main() {
	var (
		outputPath     = flag.String("output", "sota_comparison.json", "Output file for results")
		maxDocs        = flag.Int("max-docs", 5, "Maximum documents per query")
		budgetTokens   = flag.Int("budget", 4000, "Token budget for context")
		iterations     = flag.Int("iterations", 3, "Number of iterations per query")
		verbose        = flag.Bool("verbose", false, "Enable verbose logging")
		systemsFlag    = flag.String("systems", "contextlite_optimization,bm25_baseline,embedding_retrieval,llm_reranking", "Comma-separated list of systems to test")
	)
	flag.Parse()

	if *verbose {
		log.SetFlags(log.LstdFlags | log.Lshortfile)
	}

	log.Println("🚀 Starting SOTA RAG System Evaluation")
	log.Printf("Configuration: max_docs=%d, budget=%d tokens, iterations=%d", 
		*maxDocs, *budgetTokens, *iterations)

	// Parse systems to test
	systems := []string{"contextlite_optimization", "bm25_baseline", "embedding_retrieval", "llm_reranking"}
	if *systemsFlag != "" {
		// Parse comma-separated systems (simplified for demo)
		systems = []string{"contextlite_optimization", "bm25_baseline", "embedding_retrieval", "llm_reranking"}
	}

	// Configure evaluation
	config := &evaluation.ComparisonConfig{
		OutputPath:       *outputPath,
		SystemsToTest:    systems,
		QueryTypes:       []string{"factual", "analytical", "creative"},
		MaxDocuments:     *maxDocs,
		BudgetTokens:     *budgetTokens,
		RunIterations:    *iterations,
		SignificanceTest: true,
	}

	// Create SOTA comparison evaluator
	sotaEval := evaluation.NewSOTAComparison(config)

	// Run comprehensive evaluation
	ctx, cancel := context.WithTimeout(context.Background(), 10*time.Minute)
	defer cancel()

	log.Println("📊 Running SOTA comparison evaluation...")
	
	start := time.Now()
	results, err := sotaEval.RunSOTAComparison(ctx)
	if err != nil {
		log.Fatalf("❌ SOTA evaluation failed: %v", err)
	}
	
	duration := time.Since(start)
	log.Printf("✅ Evaluation completed in %v", duration)

	// Print comprehensive results
	sotaEval.PrintSummary(results)

	// Print detailed metrics for each system
	fmt.Println("\n📋 Detailed System Metrics:")
	fmt.Println("----------------------------------------")
	
	for system, metrics := range results.SystemResults {
		fmt.Printf("\n🔧 %s:\n", system)
		fmt.Printf("  Recall@1:  %.3f\n", metrics.MeanRecallAt1)
		fmt.Printf("  Recall@3:  %.3f\n", metrics.MeanRecallAt3)
		fmt.Printf("  Recall@5:  %.3f\n", metrics.MeanRecallAt5)
		fmt.Printf("  Recall@10: %.3f\n", metrics.MeanRecallAt10)
		fmt.Printf("  nDCG@1:    %.3f\n", metrics.MeanNDCG1)
		fmt.Printf("  nDCG@3:    %.3f\n", metrics.MeanNDCG3)
		fmt.Printf("  nDCG@5:    %.3f\n", metrics.MeanNDCG5)
		fmt.Printf("  nDCG@10:   %.3f\n", metrics.MeanNDCG10)
		fmt.Printf("  MAP:       %.3f\n", metrics.MeanMAP)
		fmt.Printf("  MRR:       %.3f\n", metrics.MeanMRR)
		fmt.Printf("  Precision: %.3f\n", metrics.MeanPrecision)
		fmt.Printf("  F1 Score:  %.3f\n", metrics.MeanF1Score)
		fmt.Printf("  Latency:   %.1f ms (±%.1f)\n", metrics.MeanLatencyMs, metrics.StdLatencyMs)
		fmt.Printf("  Memory:    %.1f MB\n", metrics.MeanMemoryMB)
		fmt.Printf("  Context:   %.0f tokens\n", metrics.MeanContextLen)
		fmt.Printf("  Queries:   %d\n", metrics.QueryCount)
	}

	// Print statistical insights
	fmt.Println("\n📈 Statistical Insights:")
	fmt.Println("----------------------------------------")
	
	if results.Summary.BestOverall == "contextlite_optimization" {
		fmt.Printf("🏆 ContextLite optimization achieves SOTA performance!\n")
		if results.Summary.SOTAAdvantage > 0 {
			fmt.Printf("📊 Performance advantage: +%.1f%% over next best system\n", results.Summary.SOTAAdvantage)
		}
	} else {
		fmt.Printf("📊 Best performing system: %s\n", results.Summary.BestOverall)
		if contextLiteResults, exists := results.SystemResults["contextlite_optimization"]; exists {
			if bestResults, exists := results.SystemResults[results.Summary.BestOverall]; exists {
				gap := ((bestResults.MeanRecallAt5 - contextLiteResults.MeanRecallAt5) / contextLiteResults.MeanRecallAt5) * 100
				fmt.Printf("📉 ContextLite gap: -%.1f%% behind best system\n", gap)
			}
		}
	}

	// Efficiency analysis
	if results.Summary.BestEfficiency == "contextlite_optimization" {
		fmt.Printf("⚡ ContextLite optimization is the most efficient system!\n")
	} else {
		fmt.Printf("⚡ Most efficient system: %s\n", results.Summary.BestEfficiency)
	}

	// Cross-metric analysis
	fmt.Println("\n🔍 Cross-Metric Analysis:")
	if contextLiteResults, exists := results.SystemResults["contextlite_optimization"]; exists {
		efficiency := contextLiteResults.MeanRecallAt5 / contextLiteResults.MeanLatencyMs * 1000 // Recall per second
		fmt.Printf("📊 ContextLite efficiency: %.3f Recall@5 per second\n", efficiency)
		
		qualityLatencyRatio := contextLiteResults.MeanNDCG5 / (contextLiteResults.MeanLatencyMs / 1000)
		fmt.Printf("📊 ContextLite quality/latency ratio: %.2f nDCG@5 per second\n", qualityLatencyRatio)
	}

	fmt.Printf("\n📁 Complete results saved to: %s\n", *outputPath)
	fmt.Println("🎯 SOTA evaluation complete!")
}
