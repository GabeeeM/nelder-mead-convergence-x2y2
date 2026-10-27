/-! ## Main theorem

McKinnon's question (Lagarias–Poonen–Wright, arXiv:1104.0350, §4) for f(x,y) = x² + y²:
the original Nelder–Mead algorithm with expansion steps (Algorithm NM of Lagarias–Reeds–Wright–Wright,
coefficients ρ = 1, χ = 2, γ = 1/2, σ = 1/2) converges, from every nondegenerate starting triangle,
to the minimizer: all three vertices tend to (0, 0). -/

namespace NM

/-- every vertex converges to the minimizer `0`, for every sorted nondegenerate initial triangle -/
theorem mckinnon_x2y2 (t0 : Tri) (h0 : sorted t0) (hn0 : nondeg t0) :
    Filter.Tendsto (fun k => (traj t0 k).p1) Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun k => (traj t0 k).p2) Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun k => (traj t0 k).p3) Filter.atTop (nhds 0) :=
  NMR3.nm_converges_of_reccert3 NMLoadR3.rootKT NMLoadR3.rootCerts NMLoadR3.rootOK t0 h0 hn0

/-- the same, starting from any nondegenerate triangle `(x, y, z)` ordered by function value -/
theorem mckinnon_x2y2' (x y z : Pt) (hn : nondeg ⟨x, y, z⟩) :
    Filter.Tendsto (fun k => (traj (sort3 x y z) k).p1) Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun k => (traj (sort3 x y z) k).p2) Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun k => (traj (sort3 x y z) k).p3) Filter.atTop (nhds 0) :=
  mckinnon_x2y2 _ (NMS.sort3_sorted x y z) (NMS.sort3_nondeg x y z hn)

end NM

#print axioms NM.mckinnon_x2y2
#print axioms NM.mckinnon_x2y2'
