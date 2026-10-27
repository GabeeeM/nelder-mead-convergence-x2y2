# Rigorous outer polygons for the D-shape region of a cell, in exact rationals.
#   valid shapes:  heron(a,b) = -4a^2 - 4ab - 4b^2 + 4a + 4b - 1 >= 0   (an ellipse, centre (1/3,1/3))
#   global tangent cuts  n·(a,b) <= h  with  h >= (n1+n2)/3 + (1/3) sqrt(n1^2 - n1 n2 + n2^2)
#   strip cells: additionally  n0·(a,b) >= c0, certified by a degree-2 Handelman identity
#       heron - tau - eps = nu0 + sum nu_i l_i + sum mu_ij l_i l_j   (all coefficients >= 0)
#   where l_i >= 0 are the constraints of  rect ∩ {n0·x <= c0}.
using JuMP, HiGHS

heronQ(a, b) = -4a^2 - 4a*b - 4b^2 + 4a + 4b - 1

const NTAN = 128
const DEN_N = 4096          # normals rationalized with this denominator
const DEN_H = 2^24          # supports rounded up with this denominator
function make_cuts()
    cuts = Tuple{Rational{BigInt},Rational{BigInt},Rational{BigInt}}[]
    for k in 0:NTAN-1
        θ = 2π*k/NTAN
        n1 = Rational{BigInt}(round(BigInt, cos(θ)*DEN_N), DEN_N)
        n2 = Rational{BigInt}(round(BigInt, sin(θ)*DEN_N), DEN_N)
        hs = (n1 + n2)/3 + sqrt(BigFloat(n1^2 - n1*n2 + n2^2))/3
        h = Rational{BigInt}(ceil(BigInt, hs*DEN_H) + 1, DEN_H)
        # exact validity: (h - (n1+n2)/3)^2 * 9 >= n1^2 - n1 n2 + n2^2  and  h >= (n1+n2)/3
        @assert h >= (n1+n2)/3 && 9*(h - (n1+n2)/3)^2 >= n1^2 - n1*n2 + n2^2
        push!(cuts, (n1, n2, h))
    end
    cuts
end
const CUTSQ = make_cuts()

# clip a convex polygon (list of points, Rational) by n1 x + n2 y <= h
function clipQ(poly, n1, n2, h)
    out = eltype(poly)[]
    m = length(poly); m == 0 && return out
    for i in 1:m
        P = poly[i]; Q = poly[mod1(i+1, m)]
        fP = n1*P[1] + n2*P[2] - h; fQ = n1*Q[1] + n2*Q[2] - h
        fP <= 0 && push!(out, P)
        if (fP < 0 && fQ > 0) || (fP > 0 && fQ < 0)
            t = fP / (fP - fQ); push!(out, (P[1] + t*(Q[1]-P[1]), P[2] + t*(Q[2]-P[2])))
        end
    end
    out
end
# outer polygon of {valid shapes in rect [alo,ahi]x[blo,bhi]}: rect ∩ active tangent cuts ∩ {a+b<=1}
function outer_poly(alo, ahi, blo, bhi)
    R = Rational{BigInt}
    poly = [(R(alo), R(blo)), (R(ahi), R(blo)), (R(ahi), R(bhi)), (R(alo), R(bhi))]
    poly = clipQ(poly, R(1), R(1), R(1))
    active = Int[]
    for (k, (n1, n2, h)) in enumerate(CUTSQ)
        isempty(poly) && break
        if any(p -> n1*p[1] + n2*p[2] > h, poly)
            poly = clipQ(poly, n1, n2, h); push!(active, k)
        end
    end
    poly, active
end

# monomial coefficients (1, a, b, a^2, ab, b^2) of an affine form l = c0 + c1 a + c2 b
lin_coeffs(c0, c1, c2) = (c0, c1, c2, 0, 0, 0)
function mul_lin(l, m)  # product of two affine forms -> quadratic coeffs
    (l[1]*m[1], l[1]*m[2] + l[2]*m[1], l[1]*m[3] + l[3]*m[1], l[2]*m[2], l[2]*m[3] + l[3]*m[2], l[3]*m[3])
end
# Handelman certificate for  heron - tau >= eps  on  {l_i >= 0}  (float LP); returns (eps, nu0, nu, mu) or nothing
function handelman(L, tau)
    pairs = [(i, j) for i in 1:length(L) for j in i:length(L)]
    target = (-1 - tau, 4.0, 4.0, -4.0, -4.0, -4.0)   # heron - tau
    m = Model(HiGHS.Optimizer); set_silent(m)
    @variable(m, ν0 >= 0); @variable(m, ν[1:length(L)] >= 0); @variable(m, μ[1:length(pairs)] >= 0)
    @variable(m, ε)
    for k in 1:6
        expr = (k == 1 ? ν0 : 0) + sum(ν[i]*(k <= 3 ? L[i][k] : 0.0) for i in 1:length(L)) +
               sum(μ[p]*mul_lin(L[pairs[p][1]], L[pairs[p][2]])[k] for p in 1:length(pairs))
        @constraint(m, expr + (k == 1 ? ε : 0) == target[k])
    end
    @objective(m, Max, ε); optimize!(m)
    termination_status(m) == MOI.OPTIMAL || return nothing
    (value(ε), value(ν0), value.(ν), value.(μ), pairs)
end
# inner cut for a strip rect: returns (n0, c0) or nothing if not needed / impossible
function inner_cut(alo, ahi, blo, bhi, tau)
    ac = (alo+ahi)/2; bc = (blo+bhi)/2
    g = (8ac + 4bc - 4, 4ac + 8bc - 4)          # -∇heron (outward)
    nrm = hypot(g...); nrm < 1e-12 && return nothing
    n0 = (round(g[1]/nrm*1024)/1024, round(g[2]/nrm*1024)/1024)
    corners = [(alo,blo),(ahi,blo),(ahi,bhi),(alo,bhi)]
    vals = [n0[1]*p[1] + n0[2]*p[2] for p in corners]
    # if heron <= tau on whole rect corners and center, maybe no cut needed: check max heron on rect
    lo, hi = minimum(vals), maximum(vals)
    best = nothing
    L(c0) = [(-alo, 1.0, 0.0), (ahi, -1.0, 0.0), (-blo, 0.0, 1.0), (bhi, 0.0, -1.0), (c0, -n0[1], -n0[2])]
    # bisection for the largest c0 with eps > 0
    a_, b_ = lo, hi
    for it in 1:30
        c0 = (a_ + b_)/2
        r = handelman(L(c0), tau)
        if r !== nothing && r[1] > 1e-9
            best = (n0, c0, r); a_ = c0
        else
            b_ = c0
        end
    end
    best
end

# faster inner cut: geometric c0 (min of n0·x over rect ∩ {heron <= tau}, sampled boundary), then one LP check
function inner_cut_fast(alo, ahi, blo, bhi, tau; margin=1e-4)
    ac = (alo+ahi)/2; bc = (blo+bhi)/2
    g = (8ac + 4bc - 4, 4ac + 8bc - 4); nrm = hypot(g...); nrm < 1e-12 && return nothing
    n0 = (round(g[1]/nrm*1024)/1024, round(g[2]/nrm*1024)/1024)
    # sample rect ∩ {heron <= tau}: grid + bisection to the level set along rows/cols
    cmin = Inf; n = 32
    for i in 0:n, j in 0:n
        a = alo + i/n*(ahi-alo); b = blo + j/n*(bhi-blo)
        heronQ(a, b) <= tau && (cmin = min(cmin, n0[1]*a + n0[2]*b))
    end
    for i in 0:n, j in 0:n-1
        a = alo + i/n*(ahi-alo); b1 = blo + j/n*(bhi-blo); b2 = blo + (j+1)/n*(bhi-blo)
        h1 = heronQ(a, b1) - tau; h2 = heronQ(a, b2) - tau
        if h1*h2 < 0
            lo, hi = b1, b2
            for _ in 1:50; m = (lo+hi)/2; (heronQ(a,m)-tau)*h1 > 0 ? (lo = m) : (hi = m); end
            cmin = min(cmin, n0[1]*a + n0[2]*(lo+hi)/2)
        end
        b = alo + i/n*(ahi-alo); a1 = blo + j/n*(bhi-blo)   # (reuse for columns below)
    end
    for j in 0:n, i in 0:n-1
        b = blo + j/n*(bhi-blo); a1 = alo + i/n*(ahi-alo); a2 = alo + (i+1)/n*(ahi-alo)
        h1 = heronQ(a1, b) - tau; h2 = heronQ(a2, b) - tau
        if h1*h2 < 0
            lo, hi = a1, a2
            for _ in 1:50; m = (lo+hi)/2; (heronQ(m,b)-tau)*h1 > 0 ? (lo = m) : (hi = m); end
            cmin = min(cmin, n0[1]*(lo+hi)/2 + n0[2]*b)
        end
    end
    cmin == Inf && return :empty
    L(c0) = [(-alo, 1.0, 0.0), (ahi, -1.0, 0.0), (-blo, 0.0, 1.0), (bhi, 0.0, -1.0), (c0, -n0[1], -n0[2])]
    c0 = cmin - margin
    for tries in 1:6
        r = handelman(L(c0), tau)
        (r !== nothing && r[1] > 1e-7) && return (n0, c0, r)
        c0 -= margin * 4^tries
    end
    nothing
end

# ---- data-free cuts (what the Lean checker will compute) ----
# heron(x) = heron(c) + g(c)·(x-c) - (x-c)' B (x-c),  B = [[4,2],[2,4]],  g(c) = (-8c1-4c2+4, -4c1-8c2+4)
#   outer cut (valid shapes):  g(c)·(x-c) >= -heron(c)
#   inner cut (strip, heron <= tau):  g(c)·(x-c) <= tau - heron(c) + Bmax,  Bmax = max_{corners} (x-c)'B(x-c)
function simple_poly(alo, ahi, blo, bhi, strip::Bool, tau)
    R = Rational{BigInt}
    alo, ahi, blo, bhi = R(alo), R(ahi), R(blo), R(bhi)
    c1 = (alo + ahi)/2; c2 = (blo + bhi)/2
    g1 = -8c1 - 4c2 + 4; g2 = -4c1 - 8c2 + 4
    hc = heronQ(c1, c2)
    poly = [(alo, blo), (ahi, blo), (ahi, bhi), (alo, bhi)]
    poly = clipQ(poly, R(1), R(1), R(1))                      # a + b <= 1
    # outer: -g·x <= -g·c + heron(c)
    poly = clipQ(poly, -g1, -g2, -(g1*c1 + g2*c2) + hc)
    if strip
        Bq(x, y) = 4*(x-c1)^2 + 4*(x-c1)*(y-c2) + 4*(y-c2)^2
        Bmax = maximum(Bq(p[1], p[2]) for p in ((alo,blo),(ahi,blo),(ahi,bhi),(alo,bhi)))
        poly = clipQ(poly, g1, g2, g1*c1 + g2*c2 + R(tau) - hc + Bmax)
    end
    poly
end
