#!/bin/bash

# Wizard of Oz Port Management Demonstration
# This shows the completely invisible port experience

echo "🧙‍♂️ ContextLite: Wizard of Oz Port Management"
echo "=============================================="
echo ""
echo "🎯 GOAL: Ports should be completely invisible to users"
echo "✨ EXPERIENCE: Just run contextlite and everything works"
echo ""

# Show current registry state
echo "📋 Current Port Registry State:"
echo "-------------------------------"
./build/port-registry stats
echo ""

# Demonstrate invisible allocation
echo "🎭 Starting ContextLite instances (invisible port management)..."
echo ""

# Start first instance
echo "👤 User 1: ./contextlite"
echo "🎯 Behind the scenes: Port registry allocates port..."
RESULT1=$(./build/port-registry allocate "contextlite-user1" "$(pwd)")
PORT1=$(echo "$RESULT1" | tail -1 | grep -o '"port":[0-9]*' | cut -d: -f2)
echo "   ✅ User 1: ContextLite ready at http://localhost:$PORT1"
echo ""

# Start second instance
echo "👤 User 2: ./contextlite (in different directory)"
echo "🎯 Behind the scenes: Port registry detects conflict, finds new port..."
RESULT2=$(./build/port-registry allocate "contextlite-user2" "/different/path")
PORT2=$(echo "$RESULT2" | tail -1 | grep -o '"port":[0-9]*' | cut -d: -f2)
echo "   ✅ User 2: ContextLite ready at http://localhost:$PORT2"
echo ""

# Start third instance
echo "👤 User 3: ./contextlite (yet another directory)"  
echo "🎯 Behind the scenes: Port registry finds another available port..."
RESULT3=$(./build/port-registry allocate "contextlite-user3" "/another/path")
PORT3=$(echo "$RESULT3" | tail -1 | grep -o '"port":[0-9]*' | cut -d: -f2)
echo "   ✅ User 3: ContextLite ready at http://localhost:$PORT3"
echo ""

# Show registry state with multiple allocations
echo "📊 Port Registry State (3 active instances):"
echo "---------------------------------------------"
./build/port-registry list
echo ""

# Show stats
echo "📈 Registry Statistics:"
echo "----------------------"
./build/port-registry stats
echo ""

# Simulate audit daemon cleanup
echo "🧹 Audit Daemon: Running automatic cleanup..."
echo "----------------------------------------------"
./build/port-registry cleanup
echo ""

# Show final state
echo "📋 Final Registry State:"
echo "------------------------"
./build/port-registry list
echo ""

echo "🎯 KEY BENEFITS:"
echo "✅ Users never think about ports"
echo "✅ Multiple instances work automatically"  
echo "✅ Automatic cleanup prevents port leaks"
echo "✅ Cross-platform compatibility"
echo "✅ Background audit maintains health"
echo ""

echo "🧙‍♂️ WIZARD OF OZ EFFECT:"
echo "👤 User Experience: 'It just works!'"
echo "🎭 Behind Curtain: Sophisticated port orchestration system"
echo ""

echo "🚀 RESULT: Port management is completely invisible!"
