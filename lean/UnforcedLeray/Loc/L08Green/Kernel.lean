import UnforcedLeray.Loc.L08Green.Algebra
import UnforcedLeray.Infra.HalfLineGreen
import UnforcedLeray.Infra.VolterraEvolution.Operator

/-!
# Step L8, kernels: the dichotomy data of `Infra/HalfLineGreen` from L3 and L7

Helper for `UnforcedLeray.Loc.L08Green` (step `GreenStep`, `paper/main.tex` lines 371–428,
blueprint units B1015–B1020).

From the outputs of L3 (`IsEvolution`), L6 (`IsSpectralSplitting`) and L7
(`IsPhaseProjections`) this file builds the data consumed by


* `greenKernel`: the kernels `K₋(τ,s) = E_Z(τ,s)Π₋(s)` and `K₊(τ,s) = E₊(τ,s)Π₊(s) : X → Z`
  with the bounds `loc:eq:past-bound`, `loc:eq:future-bound` (lines 398–404, taken from L7) and
  continuity in `s` in the `Z`-norm;
* `dichotomy`: the algebraic dichotomy structure (`ι = ιZ`, `Π₊`, `Π₋ = 1 - Π₊`, the evolution
  law, intertwining, and the extension `E₊` of the backward exterior evolution, line 385);
* `timeContinuous`: continuity of the kernels in `τ` in the `Z`-norm, under the hypothesis
  `hZ` that `τ ↦ E_Z(τ,σ) y` is continuous on `(σ, ∞)` in `Z` (forward smoothing is continuous
  into `H²`). This is the only input not supplied by L3: `IsEvolution` records the `X`-valued
  joint strong continuity of `E` and the size of `E_Z`, but no `Z`-norm continuity.

Continuity in `s` needs no such hypothesis: `E_Z(τ,s) = E_Z(τ,r) E(r,s)` for `s < r < τ`
(`EZ_eq_comp`, from the injectivity of `ιZ`) moves the variable `s` into the `X`-valued
evolution.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology

namespace UnforcedLeray.Blueprint.L08Green

open UnforcedLeray.Blueprint UnforcedLeray.Infra.HalfLineGreen

/-! ## `ιZ` is injective -/

theorem ιZ_injective : Function.Injective ιZ := by
  intro g g' h
  have h1 : Zclass g = Zclass g' := by rw [← Xclass_ιZ, ← Xclass_ιZ, h]
  have h2 : g.toH2 = g'.toH2 := SobolevGraph.H2.value_injective h1
  exact Subtype.ext h2

section Evolution

variable {D : BackgroundData} {c : Coefficients} {S : FreeEvolution} {ev : Evolution}
  {sp : SpectralSplitting X} {EplusZ : BackwardLift}

theorem ιZ_EZ_apply (hev : IsEvolution D c S ev) {s τ : ℝ} (h : s < τ) (x : X) :
    ιZ (ev.EZ τ s x) = ev.E τ s x :=
  DFunLike.congr_fun (hev.EZ_compat s τ h) x

theorem E_apply_E_apply (hev : IsEvolution D c S ev) {s r τ : ℝ} (h1 : s ≤ r) (h2 : r ≤ τ)
    (x : X) : ev.E τ r (ev.E r s x) = ev.E τ s x :=
  DFunLike.congr_fun (hev.law s r τ h1 h2) x

/-- `E_Z(τ,s) = E_Z(τ,r) E(r,s)` for `s < r < τ`. -/
theorem EZ_eq_comp (hev : IsEvolution D c S ev) {s r τ : ℝ} (hsr : s < r) (hrτ : r < τ) :
    ev.EZ τ s = (ev.EZ τ r).comp (ev.E r s) := by
  ext1 x
  apply ιZ_injective
  rw [ContinuousLinearMap.comp_apply, ιZ_EZ_apply hev (hsr.trans hrτ), ιZ_EZ_apply hev hrτ,
    E_apply_E_apply hev hsr.le hrτ.le]

/-- `E(r,s) Π₋(s) = Π₋(r) E(r,s)` for `s ≤ r`. -/
theorem E_apply_projMinus (hpp : IsPhaseProjections D ev sp EplusZ) {s r : ℝ} (h : s ≤ r)
    (x : X) :
    ev.E r s ((1 - exteriorProjection D.period ev sp.MplusInv s) x) =
      (1 - exteriorProjection D.period ev sp.MplusInv r) (ev.E r s x) := by
  have hi := DFunLike.congr_fun (hpp.intertwine s r h) x
  simp only [ContinuousLinearMap.comp_apply] at hi
  simp only [_root_.sub_apply, one_apply_eq_self, map_sub, hi]

/-- `E₊(τ,s)Π₊(s) = E_Z(τ,r) E₊(r,s)Π₊(s)` in `Z`, for `r < τ ≤ s`. -/
theorem EplusZ_eq_comp (hev : IsEvolution D c S ev)
    (hsp : IsSpectralSplitting (monodromy D ev) D.period D.σ sp)
    (hpp : IsPhaseProjections D ev sp EplusZ) (hP : 0 < D.period) {r τ s : ℝ} (hrτ : r < τ)
    (hτs : τ ≤ s) :
    EplusZ τ s = (ev.EZ τ r).comp (backwardExterior D.period ev sp.MplusInv r s) := by
  ext1 x
  apply ιZ_injective
  have h1 := DFunLike.congr_fun (hpp.future_lift τ s hτs) x
  have h2 := DFunLike.congr_fun (E_mul_backwardExterior hev hsp hP hrτ.le hτs) x
  rw [ContinuousLinearMap.comp_apply] at h1
  rw [ContinuousLinearMap.comp_apply, ιZ_EZ_apply hev hrτ, h1, ← h2]
  rfl

/-! ## Continuity in `X` -/

/-- `s ↦ E(τ,s) x` is continuous on `(-∞, τ]`. -/
theorem continuousOn_E_snd (hev : IsEvolution D c S ev) (τ : ℝ) (x : X) :
    ContinuousOn (fun s => ev.E τ s x) (Iic τ) :=
  (hev.strongly_continuous x).comp (continuousOn_const.prodMk continuousOn_id)
    (fun _ hs => hs)

/-- `s ↦ E₊(r,s)Π₊(s) x` is continuous on `(r, ∞)`. -/
theorem continuousOn_backwardExterior (hev : IsEvolution D c S ev)
    (hsp : IsSpectralSplitting (monodromy D ev) D.period D.σ sp)
    (hpp : IsPhaseProjections D ev sp EplusZ) (hP : 0 < D.period) (r : ℝ) (x : X) :
    ContinuousOn (fun s => backwardExterior D.period ev sp.MplusInv r s x) (Ioi r) := by
  intro s₀ hs₀
  refine ContinuousAt.continuousWithinAt ?_
  set s₁ := s₀ + 1
  have hcont : ContinuousAt (fun s => backwardExterior D.period ev sp.MplusInv r s₁
      (exteriorProjection D.period ev sp.MplusInv s₁ (ev.E s₁ s x))) s₀ := by
    have h := (continuousOn_E_snd hev s₁ x).continuousAt (Iic_mem_nhds (by linarith))
    exact ((backwardExterior D.period ev sp.MplusInv r s₁).continuous.comp
      (exteriorProjection D.period ev sp.MplusInv s₁).continuous).continuousAt.comp h
  refine hcont.congr ?_
  filter_upwards [Ioo_mem_nhds (show r < s₀ from hs₀) (show s₀ < s₁ by linarith)] with s hs
  have hb := DFunLike.congr_fun (backwardExterior_mul_E_mul_proj hev hsp hP hs.1.le hs.2.le) x
  have hi := DFunLike.congr_fun (hpp.intertwine s s₁ hs.2.le) x
  simp only [ContinuousLinearMap.comp_apply] at hi
  rw [← hb]
  change _ = backwardExterior D.period ev sp.MplusInv r s₁
    (ev.E s₁ s (exteriorProjection D.period ev sp.MplusInv s x))
  rw [hi]

/-! ## Local bound of the smoothing `E_Z` -/

/-- `‖E_Z(t,σ)‖` is bounded near any `t₀ > σ` (from the strip bounds of L3). -/
theorem eventually_norm_EZ_le (hev : IsEvolution D c S ev) {σ t₀ : ℝ} (h : σ < t₀) :
    ∃ C : ℝ, ∀ᶠ t in 𝓝 t₀, ‖ev.EZ t σ‖ ≤ C := by
  obtain ⟨C₀, hC₀⟩ := hev.strip_bounds (t₀ - σ + 1) (by linarith)
  refine ⟨|C₀| / Real.sqrt ((t₀ - σ) / 2), ?_⟩
  filter_upwards [Ioo_mem_nhds (show (σ + t₀) / 2 < t₀ by linarith)
    (show t₀ < t₀ + 1 by linarith)] with t ht
  have hσt : σ < t := by linarith [ht.1]
  have hb := ((hC₀ σ t hσt.le (by linarith [ht.2])).2 hσt).2.1
  have hpos : 0 < Real.sqrt ((t₀ - σ) / 2) := Real.sqrt_pos.2 (by linarith)
  calc ‖ev.EZ t σ‖ ≤ C₀ / Real.sqrt (t - σ) := hb
    _ ≤ |C₀| / Real.sqrt (t - σ) :=
        div_le_div_of_nonneg_right (le_abs_self C₀) (Real.sqrt_nonneg _)
    _ ≤ |C₀| / Real.sqrt ((t₀ - σ) / 2) :=
        div_le_div_of_nonneg_left (abs_nonneg _) hpos
          (Real.sqrt_le_sqrt (by linarith [ht.1]))

/-- Under `hZ`, `τ ↦ E_Z(τ,σ) v(τ)` is continuous on any `U ⊆ (σ, ∞)` where `v` is. -/
theorem continuousOn_EZ_apply (hev : IsEvolution D c S ev)
    (hZ : ∀ (σ : ℝ) (y : X), ContinuousOn (fun τ => ev.EZ τ σ y) (Ioi σ)) {σ : ℝ}
    {U : Set ℝ} (hU : U ⊆ Ioi σ) {v : ℝ → X} (hv : ContinuousOn v U) :
    ContinuousOn (fun τ => ev.EZ τ σ (v τ)) U := by
  refine UnforcedLeray.Infra.VolterraEvolution.continuousOn_clm_apply
    (fun e => (hZ σ e).mono hU) (fun t₀ ht₀ => ?_) hv
  obtain ⟨C, hC⟩ := eventually_norm_EZ_le hev (hU ht₀)
  exact ⟨C, hC.filter_mono nhdsWithin_le_nhds⟩

end Evolution

/-! ## The kernels and the dichotomy -/

section Kernel

variable {D : BackgroundData} {c : Coefficients} {S : FreeEvolution} {ev : Evolution}
  {sp : SpectralSplitting X} {EplusZ : BackwardLift}

theorem one_div_sqrt_eq_rpow {t : ℝ} (ht : 0 ≤ t) : 1 / Real.sqrt t = t ^ (-(1 / 2 : ℝ)) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_neg ht, one_div]

/-- The past kernel `K₋(τ,s) = E_Z(τ,s)Π₋(s)`. -/
def pastKernel (ev : Evolution) (period : ℝ) (N : X →L[ℝ] X) (τ s : ℝ) : X →L[ℝ] Z :=
  (ev.EZ τ s).comp (1 - exteriorProjection period ev N s)

/-- `s ↦ K₋(τ,s) x` is continuous on `(-∞, τ)` in `Z`. -/
theorem continuousOn_pastKernel (hev : IsEvolution D c S ev)
    (hpp : IsPhaseProjections D ev sp EplusZ) (τ : ℝ) (x : X) :
    ContinuousOn (fun s => pastKernel ev D.period sp.MplusInv τ s x) (Iio τ) := by
  intro s₀ hs₀
  refine ContinuousAt.continuousWithinAt ?_
  set r := (s₀ + τ) / 2
  have hs₀r : s₀ < r := by
    have : s₀ < τ := hs₀
    simp only [r]; linarith
  have hrτ : r < τ := by
    have : s₀ < τ := hs₀
    simp only [r]; linarith
  have hcont : ContinuousAt (fun s => ev.EZ τ r
      ((1 - exteriorProjection D.period ev sp.MplusInv r) (ev.E r s x))) s₀ :=
    ((ev.EZ τ r).continuous.comp
      (1 - exteriorProjection D.period ev sp.MplusInv r).continuous).continuousAt.comp
      ((continuousOn_E_snd hev r x).continuousAt (Iic_mem_nhds hs₀r))
  refine hcont.congr ?_
  filter_upwards [Iio_mem_nhds hs₀r] with s hs
  simp only [pastKernel, ContinuousLinearMap.comp_apply]
  rw [EZ_eq_comp hev hs hrτ, ContinuousLinearMap.comp_apply, E_apply_projMinus hpp hs.le]

/-- `s ↦ K₊(τ,s) x = E₊(τ,s)Π₊(s) x` is continuous on `[τ, ∞)` in `Z`. -/
theorem continuousOn_EplusZ (hev : IsEvolution D c S ev)
    (hsp : IsSpectralSplitting (monodromy D ev) D.period D.σ sp)
    (hpp : IsPhaseProjections D ev sp EplusZ) (hP : 0 < D.period) (τ : ℝ) (x : X) :
    ContinuousOn (fun s => EplusZ τ s x) (Ici τ) := by
  have h : ContinuousOn (fun s => ev.EZ τ (τ - 1)
      (backwardExterior D.period ev sp.MplusInv (τ - 1) s x)) (Ici τ) :=
    (ev.EZ τ (τ - 1)).continuous.comp_continuousOn
      ((continuousOn_backwardExterior hev hsp hpp hP (τ - 1) x).mono
        (fun s (hs : τ ≤ s) => show τ - 1 < s by linarith))
  refine h.congr (fun s (hs : τ ≤ s) => ?_)
  simp only
  rw [EplusZ_eq_comp hev hsp hpp hP (show τ - 1 < τ by linarith) hs]
  rfl

/-- The kernels of the half-line Green operator (`loc:eq:mixed-inverse`, lines 410–414), with
the constants `C₁`, `C₂` of `loc:eq:past-bound` and `loc:eq:future-bound` (L7). -/
def greenKernel (hev : IsEvolution D c S ev)
    (hsp : IsSpectralSplitting (monodromy D ev) D.period D.σ sp)
    (hpp : IsPhaseProjections D ev sp EplusZ) (hP : 0 < D.period) {C₁ C₂ : ℝ}
    (hC₁ : ∀ s τ, s < τ →
      ‖(ev.EZ τ s).comp (1 - exteriorProjection D.period ev sp.MplusInv s)‖ ≤
        C₁ * (1 + 1 / Real.sqrt (τ - s)) * Real.exp (sp.βminus * (τ - s)))
    (hC₂ : ∀ τ s, τ ≤ s → ‖EplusZ τ s‖ ≤ C₂ * Real.exp (sp.βplus * (τ - s))) :
    GreenKernel ℝ X Z where
  Km := pastKernel ev D.period sp.MplusInv
  Kp := EplusZ
  C := max C₁ C₂
  βm := sp.βminus
  βp := sp.βplus
  norm_Km_le τ s h := by
    have hb := hC₁ s τ h
    rw [one_div_sqrt_eq_rpow (sub_nonneg.2 h.le)] at hb
    have hnn : 0 ≤ (1 + (τ - s) ^ (-(1 / 2 : ℝ))) * Real.exp (sp.βminus * (τ - s)) :=
      mul_nonneg (add_nonneg zero_le_one (Real.rpow_nonneg (sub_nonneg.2 h.le) _))
        (Real.exp_pos _).le
    calc ‖pastKernel ev D.period sp.MplusInv τ s‖
        ≤ C₁ * (1 + (τ - s) ^ (-(1 / 2 : ℝ))) * Real.exp (sp.βminus * (τ - s)) := hb
      _ ≤ max C₁ C₂ * (1 + (τ - s) ^ (-(1 / 2 : ℝ))) * Real.exp (sp.βminus * (τ - s)) := by
          rw [mul_assoc, mul_assoc]
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) hnn
  norm_Kp_le τ s h :=
    (hC₂ τ s h).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le)
  continuousOn_Km τ x := continuousOn_pastKernel hev hpp τ x
  continuousOn_Kp τ x := continuousOn_EplusZ hev hsp hpp hP τ x

/-- The extension of the backward exterior evolution used by `Dichotomy`:
`E₊(τ,s)` for `τ ≤ s`, `E(τ,s)` for `s < τ` (both composed with `Π₊(s)`, line 385). -/
def extEvol (ev : Evolution) (period : ℝ) (N : X →L[ℝ] X) (τ s : ℝ) : X →L[ℝ] X :=
  if τ ≤ s then backwardExterior period ev N τ s else ev.E τ s

/-- The exponential-dichotomy data of `Infra/HalfLineGreen` (lines 383–417). -/
def dichotomy (hev : IsEvolution D c S ev)
    (hsp : IsSpectralSplitting (monodromy D ev) D.period D.σ sp)
    (hpp : IsPhaseProjections D ev sp EplusZ) (hP : 0 < D.period) {C₁ C₂ : ℝ}
    (hC₁ : ∀ s τ, s < τ →
      ‖(ev.EZ τ s).comp (1 - exteriorProjection D.period ev sp.MplusInv s)‖ ≤
        C₁ * (1 + 1 / Real.sqrt (τ - s)) * Real.exp (sp.βminus * (τ - s)))
    (hC₂ : ∀ τ s, τ ≤ s → ‖EplusZ τ s‖ ≤ C₂ * Real.exp (sp.βplus * (τ - s))) :
    Dichotomy (greenKernel hev hsp hpp hP hC₁ hC₂) where
  ι := ιZ
  E := ev.E
  Ep := extEvol ev D.period sp.MplusInv
  Pp := exteriorProjection D.period ev sp.MplusInv
  Pm s := 1 - exteriorProjection D.period ev sp.MplusInv s
  Km_eq τ s h := by
    change ιZ.comp ((ev.EZ τ s).comp _) = _
    rw [← ContinuousLinearMap.comp_assoc, hev.EZ_compat s τ h]
  Kp_eq τ s h := by
    change ιZ.comp (EplusZ τ s) = _
    rw [hpp.future_lift τ s h]
    simp only [extEvol, h, ↓reduceIte]
    exact (backwardExterior_mul_proj hev hsp hP h).symm
  E_comp τ r s h1 h2 := hev.law s r τ h1 h2
  E_comp_Ep τ r s hrτ := by
    change ev.E τ r * (extEvol ev D.period sp.MplusInv r s *
      exteriorProjection D.period ev sp.MplusInv s) =
        extEvol ev D.period sp.MplusInv τ s * exteriorProjection D.period ev sp.MplusInv s
    by_cases hτs : τ ≤ s
    · simp only [extEvol, hτs, hrτ.trans hτs, ↓reduceIte]
      rw [← mul_assoc, E_mul_backwardExterior hev hsp hP hrτ hτs]
    · by_cases hrs : r ≤ s
      · simp only [extEvol, hτs, hrs, ↓reduceIte]
        have hsτ : s ≤ τ := (not_le.1 hτs).le
        have hbi : ev.E s r * backwardExterior D.period ev sp.MplusInv r s =
            exteriorProjection D.period ev sp.MplusInv s := hpp.backward_inverse r s hrs
        have hid : exteriorProjection D.period ev sp.MplusInv s *
            exteriorProjection D.period ev sp.MplusInv s =
              exteriorProjection D.period ev sp.MplusInv s := hpp.idempotent s
        rw [← E_mul hev hrs hsτ, mul_assoc, ← mul_assoc (ev.E s r), hbi, hid]
      · simp only [extEvol, hτs, hrs, ↓reduceIte]
        rw [← mul_assoc, E_mul hev (not_le.1 hrs).le hrτ]
  Ep_eq τ s hsτ := by
    change extEvol ev D.period sp.MplusInv τ s * exteriorProjection D.period ev sp.MplusInv s =
      ev.E τ s * exteriorProjection D.period ev sp.MplusInv s
    by_cases hτs : τ ≤ s
    · have he : τ = s := le_antisymm hτs hsτ
      subst he
      simp only [extEvol, hτs, ↓reduceIte]
      rw [backwardExterior_self, E_self hev, one_mul]
      exact hpp.idempotent τ
    · simp only [extEvol, hτs, ↓reduceIte]
  Pp_add_Pm s := by
    change exteriorProjection D.period ev sp.MplusInv s +
      (1 - exteriorProjection D.period ev sp.MplusInv s) = 1
    exact add_sub_cancel _ _
  Pp_idem s := hpp.idempotent s
  Pp_comp_E τ s h := (hpp.intertwine s τ h).symm

/-- Continuity of the kernels in `τ` in the `Z`-norm, under the hypothesis `hZ`. -/
theorem timeContinuous (hev : IsEvolution D c S ev)
    (hsp : IsSpectralSplitting (monodromy D ev) D.period D.σ sp)
    (hpp : IsPhaseProjections D ev sp EplusZ) (hP : 0 < D.period) {C₁ C₂ : ℝ}
    (hC₁ : ∀ s τ, s < τ →
      ‖(ev.EZ τ s).comp (1 - exteriorProjection D.period ev sp.MplusInv s)‖ ≤
        C₁ * (1 + 1 / Real.sqrt (τ - s)) * Real.exp (sp.βminus * (τ - s)))
    (hC₂ : ∀ τ s, τ ≤ s → ‖EplusZ τ s‖ ≤ C₂ * Real.exp (sp.βplus * (τ - s)))
    (hZ : ∀ (σ : ℝ) (y : X), ContinuousOn (fun τ => ev.EZ τ σ y) (Ioi σ)) :
    (greenKernel hev hsp hpp hP hC₁ hC₂).TimeContinuous where
  Km_shift r hr x := by
    refine continuous_iff_continuousAt.2 (fun τ₀ => ?_)
    set σ := τ₀ - r / 2 with hσ
    have hU : Ioo σ (σ + r) ∈ 𝓝 τ₀ := Ioo_mem_nhds (by linarith) (by linarith)
    have hv : ContinuousOn (fun τ => (1 - exteriorProjection D.period ev sp.MplusInv σ)
        (ev.E σ (τ - r) x)) (Ioo σ (σ + r)) := by
      have h1 : ContinuousOn (fun τ => ev.E σ (τ - r) x) (Ioo σ (σ + r)) :=
        (continuousOn_E_snd hev σ x).comp (continuous_id.sub continuous_const).continuousOn
          (fun τ (hτ : τ ∈ Ioo σ (σ + r)) => show τ - r ≤ σ by linarith [hτ.2])
      exact (1 - exteriorProjection D.period ev sp.MplusInv σ).continuous.comp_continuousOn h1
    have hc := (continuousOn_EZ_apply hev hZ (fun τ (hτ : τ ∈ Ioo σ (σ + r)) => hτ.1)
      hv).continuousAt hU
    refine hc.congr ?_
    filter_upwards [hU] with τ hτ
    change ev.EZ τ σ _ = pastKernel ev D.period sp.MplusInv τ (τ - r) x
    simp only [pastKernel, ContinuousLinearMap.comp_apply]
    rw [EZ_eq_comp hev (show τ - r < σ by linarith [hτ.2]) hτ.1,
      ContinuousLinearMap.comp_apply, E_apply_projMinus hpp (show τ - r ≤ σ by linarith [hτ.2])]
  Kp s x := by
    intro τ₀ hτ₀
    have hτ₀s : τ₀ < s := hτ₀
    refine ContinuousAt.continuousWithinAt ?_
    have hU : Ioo (τ₀ - 1) s ∈ 𝓝 τ₀ := Ioo_mem_nhds (by linarith) hτ₀s
    have hc := ((hZ (τ₀ - 1) (backwardExterior D.period ev sp.MplusInv (τ₀ - 1) s x)).mono
      (Ioo_subset_Ioi_self)).continuousAt hU
    refine hc.congr ?_
    filter_upwards [hU] with τ hτ
    change ev.EZ τ (τ₀ - 1) _ = EplusZ τ s x
    rw [EplusZ_eq_comp hev hsp hpp hP hτ.1 hτ.2.le]
    rfl

end Kernel

end UnforcedLeray.Blueprint.L08Green
