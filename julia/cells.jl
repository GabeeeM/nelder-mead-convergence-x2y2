# Box-cell certificate prototype for the potential
#   G = A^γ · λ^{(1-3γ)/2} · σ(s) · q(cell),   λ = ΣD, s = λ/(λ+Δ2+Δ3), σ(s) = min(s,s1)^δ
# in the linear coordinates z = (Δ2, Δ3, D12, D13, D23) of NM on |x|^2 (vertices sorted by f).
# Projective coordinates x = z / sum(z) on the 4-simplex; boxes on a uniform grid in (x1..x4).
using Printf

const γ = 0.8
const δ = parse(Float64, get(ENV, "DELTA", "0.7"))
const S1 = 0.5          # σ(s) = min(s,S1)^δ

# ---------- exact NM step in z-coordinates ----------
# new point v = l1 p1 + l2 p2 + l3 p3 (sum l = 1). Values relative to f1: F = (0, Δ2, Δ2+Δ3)
@inline function newpt(z, l1, l2, l3)
    Δ2, Δ3, D12, D13, D23 = z
    F2 = Δ2; F3 = Δ2 + Δ3
    Q = l1*l2*D12 + l1*l3*D13 + l2*l3*D23
    fv = l2*F2 + l3*F3 - Q
    dv1 = l2*D12 + l3*D13 - Q
    dv2 = l1*D12 + l3*D23 - Q
    (fv, dv1, dv2)
end
# returns list of (zr, α, label) for the branch actually taken (exact, for a point)
function nmstep(z)
    Δ2, Δ3, D12, D13, D23 = z
    F2 = Δ2; F3 = Δ2 + Δ3
    fr, r1, r2 = newpt(z, 1.0, 1.0, -1.0)
    if fr < 0
        fe, e1, e2 = newpt(z, 1.5, 1.5, -2.0)
        (fv, v1, v2, α, lab) = fe < fr ? (fe, e1, e2, 2.0, :E) : (fr, r1, r2, 1.0, :Rx)
    elseif fr < F2
        (fv, v1, v2, α, lab) = (fr, r1, r2, 1.0, :R)
    elseif fr < F3
        fv, v1, v2 = newpt(z, 0.75, 0.75, -0.5); α = 0.5; lab = :O
    else
        fv, v1, v2 = newpt(z, 0.25, 0.25, 0.5); α = 0.5; lab = :I
    end
    reorder(fv, v1, v2, F2, D12, α, lab)
end
# vertex set {p1 (f=0), p2 (f=F2), v (f=fv)}; ties: v after old vertices
function reorder(fv, v1, v2, F2, D12, α, lab)
    if fv < 0          # v, p1, p2
        f = (fv, 0.0, F2); z2 = (0.0 - fv, F2 - 0.0, v1, v2, D12)
    elseif fv < F2     # p1, v, p2
        z2 = (fv, F2 - fv, v1, D12, v2)
    else               # p1, p2, v
        z2 = (F2, fv - F2, D12, v1, v2)
    end
    (z2, α, lab)
end

λf(z) = z[3] + z[4] + z[5]
sf(z) = λf(z) / (λf(z) + z[1] + z[2])
σf(s) = min(s, S1)^δ
heron(z) = 2*(z[3]*z[4] + z[3]*z[5] + z[4]*z[5]) - z[3]^2 - z[4]^2 - z[5]^2
logbase(z2, z, α) = γ*log(α) + (1-3γ)/2*log(λf(z2)/λf(z)) + log(σf(sf(z2))/σf(sf(z)))

# ---------- linear maps per branch ----------
# a branch: (l1,l2,l3, α, pos) ; returns 5x5 matrix M with z' = M z  (z=(Δ2,Δ3,D12,D13,D23))
function branchmat(l1, l2, l3, pos)
    # rows of fv, dv1, dv2 as linear functionals of z
    # Q = l1 l2 D12 + l1 l3 D13 + l2 l3 D23 ; F2 = Δ2 ; F3 = Δ2+Δ3
    Qr = [0, 0, l1*l2, l1*l3, l2*l3]
    fv = [l2 + l3, l3, 0, 0, 0] .- Qr
    d1 = [0, 0, l2, l3, 0] .- Qr
    d2 = [0, 0, l1, 0, l3] .- Qr
    F2 = [1.0, 0, 0, 0, 0]; D12 = [0, 0, 1.0, 0, 0]
    rows = if pos == 1
        (-fv, F2, d1, d2, D12)
    elseif pos == 2
        (fv, F2 .- fv, d1, D12, d2)
    else
        (F2, fv .- F2, D12, d1, d2)
    end
    Matrix(hcat(rows...)')
end
const COEF = Dict(:R => (1.0, 1.0, -1.0, 1.0), :Rx => (1.0, 1.0, -1.0, 1.0), :E => (1.5, 1.5, -2.0, 2.0),
                  :O => (0.75, 0.75, -0.5, 0.5), :I => (0.25, 0.25, 0.5, 0.5))
# decision functionals (z ↦ value), sign conventions as in nmstep
const L_fr   = [0.0, -1, -1, 1, 1]        # fr = K - Δ3      (fr < 0 : reflection beats best)
const L_fr2  = [-1.0, -1, -1, 1, 1]       # fr - F2
const L_fr3  = [-1.0, -2, -1, 1, 1]       # fr - F3
const L_fefr = [-0.5, -1, -1.25, 2, 2]    # fe - fr
# value of new point (relative f1) for each move, as functional
fvfun(mv) = (c = COEF[mv]; Qr = [0, 0, c[1]*c[2], c[1]*c[3], c[2]*c[3]]; [c[2]+c[3], c[3], 0, 0, 0] .- Qr)
const L_F2 = [1.0, 0, 0, 0, 0]
# all branches as (mv, pos, list of (functional, required sign)) ; sign +1 : >= 0 ; -1 : < 0
function branches()
    B = []
    push!(B, (:E, 1, [(L_fr, -1), (L_fefr, -1)]))
    push!(B, (:Rx, 1, [(L_fr, -1), (L_fefr, +1)]))
    push!(B, (:R, 2, [(L_fr, +1), (L_fr2, -1)]))
    for pos in 1:3
        conds(mv) = pos == 1 ? [(fvfun(mv), -1)] : pos == 2 ? [(fvfun(mv), +1), (fvfun(mv) .- L_F2, -1)] : [(fvfun(mv) .- L_F2, +1)]
        push!(B, (:O, pos, vcat([(L_fr2, +1), (L_fr3, -1)], conds(:O))))
        push!(B, (:I, pos, vcat([(L_fr3, +1)], conds(:I))))
    end
    B
end
const BRANCHES = branches()
const BMATS = [branchmat(COEF[b[1]][1], COEF[b[1]][2], COEF[b[1]][3], b[2]) for b in BRANCHES]
const BALPHA = [COEF[b[1]][4] for b in BRANCHES]
