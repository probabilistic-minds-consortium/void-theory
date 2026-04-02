#!/bin/bash
files=(
"void_finite_minimal" "void_gates" "void_arithmetic" "void_observer" "void_predictive_cell"
"void_probability_minimal" "void_entropy" "void_observer_alt" "void_distinguishability"
"void_learning_cell" "void_pattern" "void_metaprobability" "void_finite_bayes"
"void_finite_randomness" "void_probability_geometry" "void_geometry" "void_tensor_minimal"
"void_genesis" "void_calculus" "void_probability_operations" "void_entropy_integration"
"void_randomness" "void_resonant_ensemble" "void_observer_collapse" "void_budget_flow"
"void_sensory_transduction" "void_symmetry_movement" "void_interference_routing"
"void_distinguishability_gradients" "void_information_theory" "void_process_memory"
"void_budgeted_complexity" "void_geometry_distinguishability" "void_geometry_basis"
"void_network" "void_calculus_geometry_bridge" "void_trace" "void_time_memory_composition"
"void_temporal_memory" "void_bohr_epistemology" "void_topology_folding" "void_entropy_tunnel"
"void_resonance" "void_crisis_relocation" "void_pattern_thermo" "void_phase_orbits"
"void_neural_theory" "void_memory_trace" "void_attention_cost" "void_credit_propagation"
"void_thermal_convection" "void_pattern_algebra_extended" "void_dual_system"
"void_convergence" "void_attention_credit_bridge" "void_integrated_brain" "void_simulation"
)

for f in "${files[@]}"; do
  if [ -f "${f}.v" ]; then
    output=$(/tmp/coq-local/usr/bin/coqc -Q . "" "${f}.v" 2>&1)
    if [ $? -eq 0 ]; then
      echo "OK: ${f}.v"
    else
      echo "FAIL: ${f}.v"
      echo "$output" | head -5
    fi
  else
    echo "SKIP: ${f}.v (file not found)"
  fi
done
