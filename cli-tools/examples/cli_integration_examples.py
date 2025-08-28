#!/usr/bin/env python3
"""
Example: Using ContextLite from Claude CLI / Cursor / Rust-chain

This demonstrates how any CLI tool can integrate with ContextLite instances
started by VS Code or other means.
"""

import os
import sys
import json
import requests
from pathlib import Path

def get_project_context(project_name_or_path: str, query: str) -> dict:
    """
    Get context from ContextLite for any CLI tool.
    
    This is what you'd integrate into Claude CLI, cursor, rust-chain, etc.
    """
    
    # Import the discovery tool
    sys.path.append(str(Path(__file__).parent))
    from contextlite_cli import ContextLiteDiscovery
    
    discovery = ContextLiteDiscovery()
    
    # Find the project's ContextLite instance
    instance = discovery.find_project_instance(project_name_or_path)
    if not instance:
        return {
            'error': f'No ContextLite found for {project_name_or_path}',
            'available': [i.get('project_name') for i in discovery.discover_instances()]
        }
    
    # Query for context
    try:
        url = f"{instance['url']}/api/v1/context/assemble"
        payload = {
            'query': query,
            'max_documents': 15,
            'use_optimization': True
        }
        
        headers = {
            'Content-Type': 'application/json',
            'X-Workspace-ID': instance.get('project_name')
        }
        
        response = requests.post(url, json=payload, headers=headers, timeout=30)
        
        if response.status_code == 200:
            data = response.json()
            return {
                'success': True,
                'project': instance.get('project_name'),
                'documents': data.get('documents', []),
                'context_summary': f"Found {len(data.get('documents', []))} relevant files"
            }
        else:
            return {'error': f'Query failed: HTTP {response.status_code}'}
            
    except Exception as e:
        return {'error': f'Connection failed: {e}'}

# Example usage for different CLI tools
def claude_cli_integration_example():
    """Example: How to integrate with Claude CLI"""
    
    # Get current working directory as project
    current_project = os.getcwd()
    project_name = Path(current_project).name
    
    # User's query to Claude
    user_query = "How does authentication work in this codebase?"
    
    # Get context from ContextLite
    context = get_project_context(project_name, user_query)
    
    if 'error' in context:
        print(f"⚠️ ContextLite unavailable: {context['error']}")
        print("Continuing without enhanced context...")
        return None
    
    # Build enhanced prompt with context
    context_files = context.get('documents', [])
    context_text = "\n\n".join([
        f"File: {doc.get('path')}\n{doc.get('content', '')[:500]}..."
        for doc in context_files[:5]  # Limit to top 5 files
    ])
    
    enhanced_prompt = f"""
Based on the following codebase context:

{context_text}

User Question: {user_query}

Please provide a detailed answer using the provided code context.
"""
    
    return enhanced_prompt

def cursor_integration_example():
    """Example: How cursor could use ContextLite"""
    
    # Cursor would detect the current project
    project_path = os.getcwd()
    
    # Get context for the current file being edited
    current_file = "src/auth.rs"  # Example
    context = get_project_context(project_path, f"files related to {current_file}")
    
    if context.get('success'):
        related_files = [doc.get('path') for doc in context.get('documents', [])]
        print(f"📁 Related files found: {', '.join(related_files[:3])}")
        return related_files
    
    return []

def rust_chain_integration_example():
    """Example: How rust-chain could use ContextLite"""
    
    # rust-chain analyzing a Rust project
    project_name = "my-rust-project"
    
    # Query for specific patterns
    patterns = [
        "error handling patterns",
        "async function implementations", 
        "trait definitions",
        "main function structure"
    ]
    
    all_context = {}
    for pattern in patterns:
        context = get_project_context(project_name, pattern)
        if context.get('success'):
            all_context[pattern] = context.get('documents', [])
    
    return all_context

def main():
    """Demo the CLI integration"""
    print("🚀 ContextLite CLI Integration Demo")
    print("=" * 40)
    
    # Check if any ContextLite instances are running
    sys.path.append(str(Path(__file__).parent))
    from contextlite_cli import ContextLiteDiscovery
    
    discovery = ContextLiteDiscovery()
    instances = discovery.discover_instances()
    
    if not instances:
        print("❌ No ContextLite instances found")
        print("💡 Start ContextLite from VS Code first")
        return
    
    print(f"✅ Found {len(instances)} ContextLite instance(s)")
    
    # Demo with first available project
    project = instances[0].get('project_name')
    print(f"🔍 Testing with project: {project}")
    
    # Test query
    test_query = "main function or entry point"
    result = get_project_context(project, test_query)
    
    if result.get('success'):
        docs = result.get('documents', [])
        print(f"✅ Found {len(docs)} relevant documents")
        
        if docs:
            print("\n📄 Sample results:")
            for i, doc in enumerate(docs[:2], 1):
                path = doc.get('path', 'unknown')
                score = doc.get('score', 0)
                print(f"   {i}. {path} (relevance: {score:.3f})")
    else:
        print(f"❌ Query failed: {result.get('error')}")
    
    print(f"\n🎯 Integration Examples:")
    print(f"   Claude CLI: Use get_project_context() in your prompts")
    print(f"   Cursor: Query related files for current context")
    print(f"   Rust-chain: Analyze patterns across the codebase")

if __name__ == "__main__":
    main()
