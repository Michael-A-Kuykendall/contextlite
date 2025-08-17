# Pairwise Behavior Demonstration: Z3 SMT vs Greedy Selection

## Test Cases

### Case 1: Constrained Selection (max_docs=2)
- **Z3 Selection**: {auth-1, security-patterns-2}
- **Z3 Objective**: 4555
- **Behavior**: Z3 respects constraint and applies pairwise penalty (-403)

### Case 2: Unconstrained Selection (max_docs=3)  
- **Z3 Selection**: {auth-doc-1, auth-1, security-patterns-2}
- **Z3 Objective**: 4862
- **Behavior**: Z3 selects all candidates; pairwise penalties reduce objective from pure sum

## SMT Infrastructure Verification

### Mathematical Correctness
✅ **Constraint Modeling**: max_docs constraint enforced precisely
✅ **Pairwise Variables**: All (K choose 2) co-selection variables y_ij declared
✅ **Linking Constraints**: Equivalence y_ij ↔ (x_i ∧ x_j) satisfied exactly
✅ **Domain Encoding**: Linear bounds (>= 0, <= 1) for all variables
✅ **Objective Function**: Proper mix of utilities and pairwise penalties

### SMT-LIB2 Artifacts (Constrained Case)
**Input**: 3 document variables, 3 pairwise variables, 23 constraints
**Output**: sat, objective=4555, solution={x1=1, x2=1, x0=0}
**Verification**: Manual calculation matches Z3 result exactly

### Key Insights
1. **Pairwise Infrastructure Complete**: All relationships modeled mathematically
2. **Penalty Application**: Only active co-selections contribute penalties  
3. **Constraint Handling**: Both soft (objective) and hard (count) constraints
4. **Verifiable Results**: Complete SMT-LIB2 artifacts with manual verification

**Status**: ✅ Pairwise behavior demonstration complete
