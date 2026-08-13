#!/usr/bin/env python3
from pathlib import Path
import os, sys, tempfile

src = Path("scripts/fa_v22_cumulative_batch.py")
s = src.read_text(encoding="utf-8")
old_sha = 'expected_candidate = "238957ca57b07de9b08fbf3d6195e0ce1d82ac21aed11f8abc7980dfec6b2736"'
new_sha = 'expected_candidate = "49ab1ab094cad1475302c962cfb8517788b855cec64b7fb95c6e656d5917331c"'
old_repairs = "repairs = ['actual_scalar_graph_core_instances', 'typed_lsmul', 'real_full_plane_test_compact_support', 'commutator_kernel_contdiff_fun_prop', 'convolution_real_scalar', 'joint_graph_core_instances', 'sqrt_comp_def', 'joint_hybase_trans', 'dense_inner_scalar', 'minimal_dense_range', 'minimal_graph_projection', 'maximal_graph_projection', 'inner_conj_orientation', 'maximal_core_target', 'closure_adjoint_explicit']"
new_repairs = "repairs = ['actual_scalar_graph_core_instances', 'strong_principal_hsub_via_canonical_instances', 'strong_schrodinger_hsub_via_canonical_instances', 'typed_lsmul', 'convolution_real_scalar', 'dense_inner_scalar', 'minimal_dense_range', 'minimal_graph_projection', 'maximal_graph_projection_target', 'inner_conj_orientation', 'maximal_core_target', 'closure_adjoint_explicit']"
assert s.count(old_sha) == 1
assert s.count(old_repairs) == 1
s = s.replace(old_sha, new_sha).replace(old_repairs, new_repairs)
fd, name = tempfile.mkstemp(prefix="fa_v22_49ab_", suffix=".py")
os.close(fd)
Path(name).write_text(s, encoding="utf-8")
os.execv(sys.executable, [sys.executable, name, *sys.argv[1:]])
