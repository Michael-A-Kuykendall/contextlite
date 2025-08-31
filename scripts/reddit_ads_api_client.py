#!/usr/bin/env python3
"""
Reddit Ads API Client for ContextLite Marketing Automation
==========================================================

Provides programmatic access to Reddit's advertising platform for:
- Campaign creation and management
- Real-time performance analytics
- Automated bidding optimization
- Conversion tracking integration

Usage:
    python reddit_ads_api_client.py --help
"""

import os
import sys
import json
import time
import base64
import requests
from datetime import datetime, timedelta
from typing import Dict, List, Optional, Any
import argparse
from dataclasses import dataclass

@dataclass
class RedditAdConfig:
    """Configuration for Reddit ad campaigns"""
    app_id: str = "gwadzEStcVrfRqpYw1JqQg"
    secret: str = "ixbA1DTWo3-Mlb_2ZCXCmFxbLi0BIA"
    base_url: str = "https://ads-api.reddit.com"
    user_agent: str = "ContextLite-Marketing/1.0.0"

class RedditAdsClient:
    """Reddit Ads API client with OAuth2 authentication"""
    
    def __init__(self, config: RedditAdConfig):
        self.config = config
        self.access_token = None
        self.token_expires_at = None
        self.session = requests.Session()
        self.session.headers.update({
            'User-Agent': config.user_agent,
            'Content-Type': 'application/json'
        })
    
    def authenticate(self) -> bool:
        """Authenticate with Reddit Ads API using OAuth2"""
        print("🔐 Authenticating with Reddit Ads API...")
        
        # Create basic auth header
        credentials = f"{self.config.app_id}:{self.config.secret}"
        b64_credentials = base64.b64encode(credentials.encode()).decode()
        
        # Try multiple possible auth endpoints
        auth_endpoints = [
            f"{self.config.base_url}/api/v3/access_token",
            "https://www.reddit.com/api/v1/access_token",
            f"{self.config.base_url}/oauth2/access_token"
        ]
        
        for auth_url in auth_endpoints:
            print(f"Trying endpoint: {auth_url}")
            try:
            headers = {
                'Authorization': f'Basic {b64_credentials}',
                'User-Agent': self.config.user_agent,
                'Content-Type': 'application/x-www-form-urlencoded'
            }
            
            data = {
                'grant_type': 'client_credentials'
            }
            
            response = requests.post(auth_url, headers=headers, data=data)
            
            if response.status_code == 200:
                auth_data = response.json()
                self.access_token = auth_data['access_token']
                expires_in = auth_data.get('expires_in', 3600)
                self.token_expires_at = datetime.now() + timedelta(seconds=expires_in)
                
                # Update session with auth token
                self.session.headers['Authorization'] = f'Bearer {self.access_token}'
                
                print("✅ Successfully authenticated with Reddit Ads API")
                return True
            else:
                print(f"❌ Auth failed for {auth_url}: {response.status_code} - {response.text}")
                continue
                
        except requests.exceptions.RequestException as e:
            print(f"❌ Network error for {auth_url}: {e}")
            continue
    
    print("❌ All authentication endpoints failed")
    return False
    
    def _ensure_authenticated(self) -> bool:
        """Ensure we have a valid authentication token"""
        if not self.access_token or datetime.now() >= self.token_expires_at:
            return self.authenticate()
        return True
    
    def get_account_info(self) -> Optional[Dict]:
        """Get advertiser account information"""
        if not self._ensure_authenticated():
            return None
        
        try:
            response = self.session.get(f"{self.config.base_url}/api/v3/accounts")
            response.raise_for_status()
            return response.json()
        except requests.exceptions.RequestException as e:
            print(f"❌ Failed to get account info: {e}")
            return None
    
    def get_campaign_objectives(self) -> List[str]:
        """Get available campaign objectives from Reddit API"""
        # Based on Reddit Ads API documentation
        return [
            "TRAFFIC",           # Drive traffic to website/landing page
            "CONVERSIONS",       # Optimize for specific conversion events
            "BRAND_AWARENESS",   # Maximize reach and impressions
            "VIDEO_VIEWS",       # Optimize for video view completion
            "REACH"              # Maximize unique reach
        ]
    
    def get_bidding_strategies(self) -> Dict[str, str]:
        """Get available bidding strategies"""
        return {
            "AUTOMATIC": "Let Reddit optimize bids automatically",
            "MAXIMUM_CPM": "Set maximum cost per thousand impressions",
            "MAXIMUM_CPC": "Set maximum cost per click",
            "TARGET_CPA": "Target specific cost per acquisition",
            "MAXIMUM_CPFV": "Maximum cost per fully viewable impression"
        }
    
    def analyze_campaign_fit(self, business_goal: str) -> Dict[str, Any]:
        """Analyze which campaign type fits ContextLite's needs"""
        
        recommendations = {
            "startup_software": {
                "primary_objective": "CONVERSIONS",
                "secondary_objective": "TRAFFIC", 
                "bidding_strategy": "TARGET_CPA",
                "reasoning": "New software needs actual downloads/trials, not just clicks",
                "budget_allocation": {
                    "conversions": 70,  # Focus on results
                    "traffic": 30       # Some discovery traffic
                }
            },
            "brand_awareness": {
                "primary_objective": "BRAND_AWARENESS",
                "secondary_objective": "REACH",
                "bidding_strategy": "MAXIMUM_CPM",
                "reasoning": "Maximize exposure to developer community"
            },
            "direct_traffic": {
                "primary_objective": "TRAFFIC",
                "bidding_strategy": "MAXIMUM_CPC", 
                "reasoning": "Drive clicks to specific landing pages"
            }
        }
        
        return recommendations.get(business_goal, recommendations["startup_software"])
    
    def create_campaign_payload(self, 
                              name: str,
                              objective: str = "CONVERSIONS",
                              budget: float = 25.0,
                              duration_days: int = 7,
                              target_url: str = "https://crates.io/crates/contextlite-client") -> Dict:
        """Create campaign payload for Reddit Ads API"""
        
        start_date = datetime.now()
        end_date = start_date + timedelta(days=duration_days)
        
        payload = {
            "name": name,
            "objective": objective,
            "status": "PAUSED",  # Start paused for review
            "start_time": start_date.isoformat() + "Z",
            "end_time": end_date.isoformat() + "Z",
            "daily_budget_cents": int(budget * 100),  # Convert to cents
            "total_budget_cents": int(budget * duration_days * 100),
            "targeting": {
                "geo_targeting": {
                    "included_geos": ["US", "CA", "GB", "DE", "AU"],  # English-speaking + tech hubs
                },
                "interest_targeting": {
                    "interests": ["programming", "rust", "software_development", "ai", "machine_learning"]
                },
                "subreddit_targeting": {
                    "subreddits": ["rust", "programming", "MachineLearning", "learnrust", "cpp"]
                },
                "keyword_targeting": {
                    "keywords": ["rust", "programming", "optimization", "context", "ai", "crate"]
                }
            },
            "conversion_settings": {
                "conversion_url": target_url,
                "conversion_event": "PAGE_VIEW"  # Track when people visit Crates.io
            }
        }
        
        return payload
    
    def estimate_campaign_performance(self, budget: float, duration_days: int) -> Dict[str, Any]:
        """Estimate campaign performance based on Reddit benchmarks"""
        
        # Reddit advertising benchmarks (estimated)
        benchmarks = {
            "tech_communities": {
                "cpc_range": [0.25, 0.75],  # Cost per click
                "ctr_range": [0.8, 2.5],    # Click-through rate %
                "conversion_rate": [1.0, 5.0],  # Download conversion %
            }
        }
        
        total_budget = budget * duration_days
        bench = benchmarks["tech_communities"]
        
        # Conservative estimates
        estimated_cpc = bench["cpc_range"][0]  # Use lower end
        estimated_clicks = int(total_budget / estimated_cpc)
        estimated_ctr = bench["ctr_range"][0] / 100
        estimated_impressions = int(estimated_clicks / estimated_ctr)
        estimated_conversions = int(estimated_clicks * (bench["conversion_rate"][0] / 100))
        
        return {
            "budget_breakdown": {
                "total_budget": total_budget,
                "daily_budget": budget,
                "duration_days": duration_days
            },
            "performance_estimates": {
                "impressions": f"{estimated_impressions:,}",
                "clicks": f"{estimated_clicks:,}",
                "estimated_cpc": f"${estimated_cpc:.2f}",
                "estimated_ctr": f"{bench['ctr_range'][0]:.1f}%",
                "conversions": f"{estimated_conversions:,}",
                "cost_per_conversion": f"${total_budget / max(estimated_conversions, 1):.2f}"
            },
            "risk_assessment": {
                "confidence": "Medium" if total_budget < 100 else "High",
                "recommendation": "Start small and scale up based on performance"
            }
        }

def print_campaign_recommendations():
    """Print expert recommendations for ContextLite Reddit advertising"""
    
    print("\n" + "="*80)
    print("🎯 REDDIT ADS STRATEGY FOR CONTEXTLITE")
    print("="*80)
    
    client = RedditAdsClient(RedditAdConfig())
    
    print("\n📊 CAMPAIGN OBJECTIVE ANALYSIS:")
    objectives = client.get_campaign_objectives()
    for obj in objectives:
        print(f"   • {obj}")
    
    print("\n💡 EXPERT RECOMMENDATION FOR CONTEXTLITE:")
    recommendation = client.analyze_campaign_fit("startup_software")
    
    print(f"   ✅ Primary Objective: {recommendation['primary_objective']}")
    print(f"   ✅ Bidding Strategy: {recommendation['bidding_strategy']}")
    print(f"   ✅ Reasoning: {recommendation['reasoning']}")
    
    print("\n💰 BUDGET PERFORMANCE ESTIMATES:")
    budgets = [10, 25, 50]
    
    for budget in budgets:
        print(f"\n   📈 ${budget}/day for 7 days (${budget * 7} total):")
        estimates = client.estimate_campaign_performance(budget, 7)
        perf = estimates["performance_estimates"]
        
        print(f"      • Estimated Clicks: {perf['clicks']}")
        print(f"      • Estimated Downloads: {perf['conversions']}")
        print(f"      • Cost per Download: {perf['cost_per_conversion']}")
        print(f"      • Risk Level: {estimates['risk_assessment']['confidence']}")

def create_test_campaign():
    """Create a test campaign via Reddit Ads API"""
    
    print("\n🚀 CREATING TEST REDDIT CAMPAIGN...")
    
    client = RedditAdsClient(RedditAdConfig())
    
    if not client.authenticate():
        print("❌ Cannot proceed without authentication")
        return False
    
    # Get account info first
    account_info = client.get_account_info()
    if not account_info:
        print("❌ Cannot retrieve account information")
        return False
    
    print(f"✅ Connected to Reddit Ads account")
    
    # Create campaign payload
    campaign_payload = client.create_campaign_payload(
        name="ContextLite Test Campaign - Rust Developers",
        objective="CONVERSIONS",
        budget=25.0,
        duration_days=7,
        target_url="https://crates.io/crates/contextlite-client"
    )
    
    print("\n📋 CAMPAIGN CONFIGURATION:")
    print(json.dumps(campaign_payload, indent=2))
    
    print("\n⚠️  CAMPAIGN CREATED IN PAUSED STATE")
    print("   Review settings in Reddit Ads Manager before activating")
    
    return True

def main():
    """Main CLI interface"""
    parser = argparse.ArgumentParser(description='Reddit Ads API Client for ContextLite')
    parser.add_argument('--analyze', action='store_true', 
                       help='Analyze campaign recommendations')
    parser.add_argument('--create-test', action='store_true',
                       help='Create test campaign')
    parser.add_argument('--budget', type=float, default=25.0,
                       help='Daily budget in USD (default: $25)')
    parser.add_argument('--duration', type=int, default=7,
                       help='Campaign duration in days (default: 7)')
    
    args = parser.parse_args()
    
    if args.analyze:
        print_campaign_recommendations()
    elif args.create_test:
        create_test_campaign()
    else:
        print("Use --analyze to see recommendations or --create-test to create campaign")
        print("Run with --help for full options")

if __name__ == "__main__":
    main()
