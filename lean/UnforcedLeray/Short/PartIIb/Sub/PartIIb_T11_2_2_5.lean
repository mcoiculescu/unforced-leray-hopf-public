import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T11_2_2
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T11_2_1

/-!
# Part II-b, leaf `PartII-b:T11/2/2/5` (`DualMainLimit`): decomposition (conditional)

Source: `the November 2 reference manuscript` 1923-1927.

The `L`-dependence of the main term is the scalar factor `φ(η/L)`:
`pairC b (dualMain φ L) = φ(η/L) · G`, `G := pairC b (dualMain 1 1)`.  Dominated convergence
(`φ(η/L) → φ 0 = 1`, `|φ| ≤ 1`, dominating function `‖G‖`) reduces everything to `G`.

Leaves (`/1`, `/2`, `/3`):
* `DualPerpBridge`: `perpC` of the cast of `H(s-·,·)` is the cast of `perpGrad` (`H` smooth for `τ>0`);
* `DualMainInfIntegrable`: `G` is `ageμ c 0`-integrable;
* `DualMainFubini`: `∫ G d(ageμ c 0) = -∫_{(0,s)} χ'(σ) F(σ) dσ` (Fubini).

Proved here: `dualMainLimit_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- **Leaf `T11/2/2/5/1`** (bridge): for `x.1 < s` (so `s - x.1 > 0`, where `HeatSol.smooth`
makes `H` jointly differentiable at `(s - x.1, x.2)`), the chain rule gives
`perpC (fun z => (H (s - z.1, z.2) : ℂ)) x i = ((perpGrad (fun p => H (s - x.1, p)) x.2 i : ℝ) : ℂ)`
(`cpdC 2`/`cpdC 1` are the `η`/`q` partials; `fderiv` of `ofReal ∘ f` is `ofReal ∘ fderiv f`
(`HasFDerivAt.ofReal_comp`), and the `s`-slice shift does not affect the `(q, η)` partials). -/
def DualPerpBridge : Prop :=
  ∀ (c ν r' : ℝ) (H : Coord → ℝ) (s : ℝ), 0 < c → 0 < ν → HeatSol c ν r' H →
    ∀ (x : Coord) (i : Fin 2), x.1 < s →
      perpC (fun z => (H (s - z.1, z.2) : ℂ)) x i =
        ((perpGrad (fun p => H (s - x.1, p)) x.2 i : ℝ) : ℂ)

/-- **Leaf `T11/2/2/5/2`** (integrability of the `L`-independent main term, SP 1923-1927):
`G = pairC b (dualMain μ χ 1 H s 1)` is `ageμ c 0`-integrable.  Proof: `G` vanishes unless
`x.1 ∈ tsupport χ ⊂ (0,s)`; bridge gives `‖G x‖ ≤ 2 σ^{Re μ} ‖χ'(σ)‖ ‖b(σ,p)‖ ‖perpGrad H(s-σ,·)(p)‖`;
`ageμ c 0` is `dσ|_{σ>0} ⊗ avgμ c` (`Axi.lintegral_ageμ`); Hölder in `p` as in
`DualFPointwise`, then `SigmaHolder` with `DualFABMeas`, `DualFAFinite`, `DualFBFinite`
(`Sub/PartIIb_T11_2_1.lean`).  Also needs `AEStronglyMeasurable G` (product of `b` with a
continuous-in-`(σ,p)` factor on `supp χ × ℝ²`). -/
def DualMainInfIntegrable : Prop :=
  DualPerpBridge → ∀ (c r ν : ℝ) (μ : ℂ) (b : CProf) (H : Coord → ℝ) (s : ℝ) (χ : ℝ → ℝ),
    0 < c → 0 < ν → 1 < r → 0 < s → InHr c r b → HeatSol c ν (r / (r - 1)) H → DFChi s χ →
    Integrable (fun x => pairC b (dualMain μ χ (fun _ => (1 : ℝ)) H s 1) x) (Axi.ageμ c 0)

/-- **Leaf `T11/2/2/5/3`** (Fubini identification): for integrable `G` (as above),
`∫ G d(ageμ c 0) = -∫_{σ ∈ (0,s)} χ'(σ) dualF c μ b H s σ`.  Proof: `ageμ c 0` is the product
`(dσ|_{σ>0}) ⊗ avgμ c` (`Axi.lintegral_ageμ` is the `lintegral` form; derive a Bochner form with
`integral_prod`/`integral_withDensity`); inner integral over `p` is `-σ^μ χ'(σ) ∫ Σ bᵢ ∇^⊥H_i d avgμ`
by the bridge; `χ' = 0` off `Ioo 0 s` (`tsupport χ ⊂ Ioo 0 s`, `deriv` vanishes off the
`tsupport`). -/
def DualMainFubini : Prop :=
  DualPerpBridge → ∀ (c r ν : ℝ) (μ : ℂ) (b : CProf) (H : Coord → ℝ) (s : ℝ) (χ : ℝ → ℝ),
    0 < c → 0 < ν → 1 < r → 0 < s → InHr c r b → HeatSol c ν (r / (r - 1)) H → DFChi s χ →
    Integrable (fun x => pairC b (dualMain μ χ (fun _ => (1 : ℝ)) H s 1) x) (Axi.ageμ c 0) →
    ∫ x, pairC b (dualMain μ χ (fun _ => (1 : ℝ)) H s 1) x ∂(Axi.ageμ c 0) =
      -∫ σ in Ioo (0 : ℝ) s, ((deriv χ σ : ℝ) : ℂ) * dualF c μ b H s σ

/-- Scalar factorization of the main term. -/
theorem pairC_dualMain (μ : ℂ) (χ φ : ℝ → ℝ) (H : Coord → ℝ) (s L : ℝ) (b : CProf) (x : Coord) :
    pairC b (dualMain μ χ φ H s L) x =
      (φ (x.2.2 / L) : ℂ) * pairC b (dualMain μ χ (fun _ => (1 : ℝ)) H s 1) x := by
  simp only [pairC, dualMain, Complex.ofReal_one, one_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **Target** `DualMainLimit` from its three leaves. -/
theorem dualMainLimit_of (h1 : DualPerpBridge) (h2 : DualMainInfIntegrable)
    (h3 : DualMainFubini) : DualMainLimit := by
  intro c r ν μ b H s χ φ hc hν hr hs hb hfl hH hχ hφ
  have hG := h2 h1 c r ν μ b H s χ hc hν hr hs hb hH hχ
  have hφc : Continuous φ := hφ.1.continuous
  have hint : ∀ L : ℝ, Integrable (fun x => pairC b (dualMain μ χ φ H s L) x) (Axi.ageμ c 0) := by
    intro L
    have hm : Continuous fun x : Coord => (φ (x.2.2 / L) : ℂ) :=
      Complex.continuous_ofReal.comp (hφc.comp (continuous_snd.comp continuous_snd |>.div_const L))
    have hb' : ∀ x, ‖pairC b (dualMain μ χ φ H s L) x‖ ≤
        ‖pairC b (dualMain μ χ (fun _ => (1 : ℝ)) H s 1) x‖ := by
      intro x
      rw [pairC_dualMain, norm_mul, Complex.norm_real]
      exact mul_le_of_le_one_left (norm_nonneg _) (by simpa [Real.norm_eq_abs] using hφ.2.2.2 _)
    refine Integrable.mono hG.norm ?_ (Filter.Eventually.of_forall fun x => (hb' x).trans_eq (norm_norm _).symm)
    exact (hm.aestronglyMeasurable.mul hG.aestronglyMeasurable).congr
      (Filter.Eventually.of_forall fun x => (pairC_dualMain μ χ φ H s L b x).symm)
  refine ⟨fun L _ => hint L, ?_⟩
  rw [← h3 h1 c r ν μ b H s χ hc hν hr hs hb hH hχ hG]
  have hlim : Tendsto (fun L : ℝ => ∫ x, pairC b (dualMain μ χ φ H s L) x ∂(Axi.ageμ c 0)) atTop
      (𝓝 (∫ x, pairC b (dualMain μ χ (fun _ => (1 : ℝ)) H s 1) x ∂(Axi.ageμ c 0))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x => ‖pairC b (dualMain μ χ (fun _ => (1 : ℝ)) H s 1) x‖) ?_ ?_ hG.norm ?_
    · refine Filter.Eventually.of_forall fun L => ?_
      exact (hint L).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun L => Filter.Eventually.of_forall fun x => ?_
      rw [pairC_dualMain, norm_mul, Complex.norm_real]
      exact mul_le_of_le_one_left (norm_nonneg _) (by simpa [Real.norm_eq_abs] using hφ.2.2.2 _)
    · refine Filter.Eventually.of_forall fun x => ?_
      have h0 : Tendsto (fun L : ℝ => x.2.2 / L) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      have : Tendsto (fun L : ℝ => (φ (x.2.2 / L) : ℂ)) atTop (𝓝 ((φ 0 : ℝ) : ℂ)) :=
        (Complex.continuous_ofReal.tendsto _).comp ((hφc.tendsto 0).comp h0)
      rw [hφ.2.2.1] at this
      have h2 := this.mul_const (pairC b (dualMain μ χ (fun _ => (1 : ℝ)) H s 1) x)
      rw [Complex.ofReal_one, one_mul] at h2
      exact h2.congr fun L => (pairC_dualMain μ χ φ H s L b x).symm
  exact hlim

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.dualMainLimit_of
