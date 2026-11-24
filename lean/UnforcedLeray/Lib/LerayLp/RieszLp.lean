import UnforcedLeray.Lib.LerayLp.RieszCZ

/-!
# The Riesz pairs `R_iR_k` on `L^p(R³)`, `1 < p < ∞` (INF01 T13, part 2)

Blueprint: INF01 target T13 (`rieszPairLp`) of

`scoping/README.md` §3. Manuscript: `R_iR_k = ∂_i∂_k(-Δ)^{-1}` (`paper/main.tex`
lines 107–111) is bounded on `L^q(R³)` for `1 < q < ∞` (unit B0414, lines 7336–7344, citing
Grafakos Cor. 5.2.8), and the operators at different exponents are consistent on the
intersections (unit B0430, lines 3720–3732).

* `rieszPairLp i k p hp1 hp`: the bounded operator on `L^p(R³)`, obtained from the
  Calderón–Zygmund theorem `CZ.extendLp` (`Lib/CZCore`, T12) applied to the transported
  operator `rieszFin i k` (T13 part 1) and conjugated back to `Space`;
* `rieszPairLp_toLp_ae`, `rieszPairLp_ae_of_memLp_two`: on `L² ∩ L^p` it is the `L²`
  operator `rieszPairL2 i k` of `Lib/CZL2` (hence the Newton Hessian `∂ᵢ∂ₖ(N ∗ ·)` on tests);
* `rieszPairLp_two`: at `p = 2` it is `rieszPairL2 i k`;
* `rieszPairLp_consistent`: for `f ∈ L^p ∩ L^q` the two operators agree a.e.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace UnforcedLeray.RieszLp

/-- The `L^p` extension of `rieszFin i k` on `Fin 3 → ℝ` (Calderón–Zygmund theorem, T12). -/
def rieszFinLp (i k : Fin 3) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp1 : 1 < p) (hp : p ≠ ⊤) :
    Lp ℝ p (volume : Measure (Fin 3 → ℝ)) →L[ℝ] Lp ℝ p (volume : Measure (Fin 3 → ℝ)) :=
  CZ.extendLp (rieszFin_isCZConvolution i k) (rieszFin_isCZConvolution k i)
    (integral_rieszFin_mul i k) p hp1 hp

/-- **INF01 T13.** The Riesz pair `R_iR_k = ∂ᵢ∂ₖ(-Δ)^{-1}` as a bounded operator on
`L^p(R³)`, `1 < p < ∞` (`paper/main.tex` lines 107–111, 7336–7344). -/
def rieszPairLp (i k : Fin 3) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp1 : 1 < p) (hp : p ≠ ⊤) :
    Lp ℝ p (volume : Measure Space) →L[ℝ] Lp ℝ p (volume : Measure Space) :=
  (ofFinLp p).comp ((rieszFinLp i k p hp1 hp).comp (toFinLp p))

theorem rieszPairLp_apply (i k : Fin 3) (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp1 : 1 < p) (hp : p ≠ ⊤)
    (f : Lp ℝ p (volume : Measure Space)) :
    rieszPairLp i k p hp1 hp f = ofFinLp p (rieszFinLp i k p hp1 hp (toFinLp p f)) := rfl

/-- `ofFinLp` respects a.e. equality across exponents. -/
theorem ofFinLp_ae_congr {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {u : Lp ℝ p (volume : Measure (Fin 3 → ℝ))} {v : Lp ℝ q (volume : Measure (Fin 3 → ℝ))}
    (h : (u : (Fin 3 → ℝ) → ℝ) =ᵐ[volume] v) :
    (ofFinLp p u : Space → ℝ) =ᵐ[volume] ofFinLp q v := by
  filter_upwards [coeFn_ofFinLp p u, coeFn_ofFinLp q v,
    mp_ofLp.quasiMeasurePreserving.ae_eq_comp h] with z h1 h2 h3
  rw [h1, h2]
  exact h3

/-- `toFinLp` respects a.e. equality across exponents. -/
theorem toFinLp_ae_congr {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {u : Lp ℝ p (volume : Measure Space)} {v : Lp ℝ q (volume : Measure Space)}
    (h : (u : Space → ℝ) =ᵐ[volume] v) :
    (toFinLp p u : (Fin 3 → ℝ) → ℝ) =ᵐ[volume] toFinLp q v := by
  filter_upwards [coeFn_toFinLp p u, coeFn_toFinLp q v,
    mp_toLp.quasiMeasurePreserving.ae_eq_comp h] with z h1 h2 h3
  rw [h1, h2]
  exact h3

/-- **INF01 T13.** On `L² ∩ L^p`, `rieszPairLp i k p` agrees a.e. with the `L²` operator
`rieszPairL2 i k` (function form). -/
theorem rieszPairLp_toLp_ae (i k : Fin 3) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp1 : 1 < p) (hp : p ≠ ⊤)
    {f : Space → ℝ} (hfp : MemLp f p volume) (hf2 : MemLp f 2 volume) :
    (rieszPairLp i k p hp1 hp (hfp.toLp f) : Space → ℝ) =ᵐ[volume]
      rieszPairL2 i k (hf2.toLp f) := by
  set F2 := toFinLp 2 (hf2.toLp f) with hF2
  have hF2f : (F2 : (Fin 3 → ℝ) → ℝ) =ᵐ[volume] f ∘ WithLp.toLp 2 := by
    filter_upwards [coeFn_toFinLp 2 (hf2.toLp f),
      mp_toLp.quasiMeasurePreserving.ae_eq_comp hf2.coeFn_toLp] with x h1 h2
    rw [h1]
    exact h2
  have hcomp := hfp.comp_measurePreserving mp_toLp
  have hF2p : MemLp (F2 : (Fin 3 → ℝ) → ℝ) p volume := hcomp.ae_eq hF2f.symm
  have e1 : toFinLp p (hfp.toLp f) = hF2p.toLp F2 := by
    rw [toFinLp_toLp]
    exact MemLp.toLp_congr _ _ hF2f.symm
  have h1 := CZ.extendLp_apply (rieszFin_isCZConvolution i k) (rieszFin_isCZConvolution k i)
    (integral_rieszFin_mul i k) p hp1 hp F2 hF2p
  have h2 : rieszFin i k F2 = toFinLp 2 (rieszPairL2 i k (hf2.toLp f)) := by
    rw [rieszFin_apply, hF2, ofFinLp_toFinLp]
  rw [rieszPairLp_apply, e1]
  have h3 := ofFinLp_ae_congr (p := p) (q := 2) (u := rieszFinLp i k p hp1 hp (hF2p.toLp F2))
    (v := rieszFin i k F2) h1
  rw [h2, ofFinLp_toFinLp] at h3
  exact h3

/-- **INF01 T13.** On `L² ∩ L^p`, `rieszPairLp i k p` agrees a.e. with `rieszPairL2 i k`
(`L^p`-element form). -/
theorem rieszPairLp_ae_of_memLp_two (i k : Fin 3) {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp1 : 1 < p)
    (hp : p ≠ ⊤) (f : Lp ℝ p (volume : Measure Space)) (hf2 : MemLp f 2 volume) :
    (rieszPairLp i k p hp1 hp f : Space → ℝ) =ᵐ[volume] rieszPairL2 i k (hf2.toLp f) := by
  have h := rieszPairLp_toLp_ae i k hp1 hp (Lp.memLp f) hf2
  rwa [Lp.toLp_coeFn] at h

/-- **INF01 T13.** At `p = 2`, `rieszPairLp` is the `L²` operator `rieszPairL2`. -/
theorem rieszPairLp_two (i k : Fin 3) :
    rieszPairLp i k 2 ENNReal.one_lt_two ENNReal.ofNat_ne_top = rieszPairL2 i k := by
  ext1 f
  apply Lp.ext
  have h := rieszPairLp_ae_of_memLp_two i k ENNReal.one_lt_two ENNReal.ofNat_ne_top f (Lp.memLp f)
  rwa [Lp.toLp_coeFn] at h

/-- **INF01 T13 (consistency across exponents).** For `f ∈ L^p ∩ L^q` the operators at `p` and
at `q` agree a.e. (unit B0430, `paper/main.tex` lines 3720–3732). -/
theorem rieszPairLp_consistent (i k : Fin 3) {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hp1 : 1 < p) (hp : p ≠ ⊤) (hq1 : 1 < q) (hq : q ≠ ⊤) {f : Space → ℝ}
    (hfp : MemLp f p volume) (hfq : MemLp f q volume) :
    (rieszPairLp i k p hp1 hp (hfp.toLp f) : Space → ℝ) =ᵐ[volume]
      rieszPairLp i k q hq1 hq (hfq.toLp f) := by
  rw [rieszPairLp_apply, rieszPairLp_apply, toFinLp_toLp, toFinLp_toLp]
  exact ofFinLp_ae_congr (CZ.extendLp_consistent (rieszFin_isCZConvolution i k)
    (rieszFin_isCZConvolution k i) (integral_rieszFin_mul i k) hp1 hp hq1 hq
    (hfp.comp_measurePreserving mp_toLp) (hfq.comp_measurePreserving mp_toLp))

end UnforcedLeray.RieszLp
