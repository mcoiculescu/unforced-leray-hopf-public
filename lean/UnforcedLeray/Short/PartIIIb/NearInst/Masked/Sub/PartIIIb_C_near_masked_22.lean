import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Lemmas

/-!
# `stripKernelBound_of_parts`: decomposition of the partial-strip kernel estimate (source 3996-4005)

Source of record: `the November 2 reference manuscript`.

For a bin `l < r ≤ e^{δ/2}l`, `r ≤ S = ε^{-b}`, and a box tensor `f` supported in `t ≥ e^δ l`:

* `StripSplit` (3996-4000): on the output band `l ≤ s < r` the strip kernel `fullOut - farOut`
  (mask `e^δ l ≤ t ≤ e^δ s`) only sees the input age `t < e^δ r`: it equals the same difference for
  `f'' = 1_{t < e^δ r} f` (all pairs are separated, so all integrals converge absolutely).
* `StripNear` (4000-4003): `fullOut f''` on the band: the source is supported in `|z'| ≤ r_o` and
  observed at `|y'| ≥ r_i`, `r_i - r_o ≥ (1 - e^{-δ/4})R/√r`, so `sep:young` (`j = 0`, `p = q = 2`,
  `b = 1`) gives `C D^{-1} = C ε √r`; the polynomial factor `P_ν` absorbs the cell/period constants.
* `StripFar` (4003-4005): `farOut f''` on the band keeps `e^δ s < t < e^δ r` (gap `δ`) and is
  bounded through the pointwise majorant `C|x|^{-4}` with `L¹` tail `C/d`, the dilation power
  `λ^{2Re μ+1/2}`, Young and the normalized-phase Minkowski step.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint.Planar

/-- The truncation `1_{t < T} f` of a chart tensor to input ages below `T`. -/
def truncAbove (T : ℝ) (f : Chart → Ten3) : Chart → Ten3 :=
  fun p => if p.1 < T then f p else 0

/-- **Strip split** (source 3996-4000): on the band `l ≤ s < r` (`r ≤ S`) the strip kernel of a box
tensor `f` supported in `t ≥ e^δ l` equals the strip kernel of `1_{t<e^δ r} f`.  Both sides are the
kernel integral against `f` restricted to `e^δ l ≤ t ≤ e^δ s`; every integral converges
absolutely since the pairs are separated (`t ≥ e^δ l > e^{δ/2} s`). -/
def StripSplit : Prop :=
  ∀ (R c ν μ δ S l r : ℝ), 0 < R → 0 < c → 0 < ν → μ ∈ Ioo (0 : ℝ) (1 / 4) → 0 < δ →
    0 < l → l < r → r ≤ Real.exp (δ / 2) * l → r ≤ S →
    ∀ f : Chart → Ten3, IsBoxTensor f → (∀ x, f x ≠ 0 → Real.exp δ * l ≤ x.1) →
      ∀ x ∈ ageBand l r,
        fullOut R c ν μ f x - farOut R c ν μ δ S f x =
          fullOut R c ν μ (truncAbove (Real.exp δ * r) f) x -
            farOut R c ν μ δ S (truncAbove (Real.exp δ * r) f) x

/-- **Strip, near part** (source 4000-4003): for a box tensor `g` supported in
`e^δ l ≤ t < e^δ r`, `‖1_{l≤s<r} fullOut g‖_H ≤ P_ν ε√r ‖g‖_{H_T}` (`sep:young` with `p = q = 2`,
`b = 1`, receivers `|y'| ≥ R/√r`, sources `|z'| ≤ R/√(e^δ l)`). -/
def StripNear : Prop :=
  ∀ Kset : Set ℝ, IsCompact Kset → Kset ⊆ Ioo 0 (1 / 4) → ∀ dm dp : ℝ, 0 < dm →
    ∀ b δ : ℝ, 0 < b → b < 1 → 0 < δ →
    ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ μ ∈ Kset, ∀ l r : ℝ, 0 < l → l < r → r ≤ Real.exp (δ / 2) * l → r ≤ p.ε ^ (-b) →
      ∀ g : Chart → Ten3, IsBoxTensor g →
        (∀ x, g x ≠ 0 → Real.exp δ * l ≤ x.1 ∧ x.1 < Real.exp δ * r) →
        AEStronglyMeasurable ((ageBand l r).indicator (fullOut p.R p.c p.ν μ g))
            (ageμ p.c (-3 / 2)) ∧
          eLpNorm ((ageBand l r).indicator (fullOut p.R p.c p.ν μ g)) 2 (ageμ p.c (-3 / 2)) ≤
            ENNReal.ofReal (C * p.ν⁻¹ ^ k * (p.ε * Real.sqrt r)) *
              eLpNorm g 2 (ageμ p.c (-1 / 2))

/-- **Strip, far part** (source 4003-4005): same hypotheses as `StripNear`, for the masked far
kernel `farOut` (inputs `e^δ s < t < e^δ r`, gap `δ`). -/
def StripFar : Prop :=
  ∀ Kset : Set ℝ, IsCompact Kset → Kset ⊆ Ioo 0 (1 / 4) → ∀ dm dp : ℝ, 0 < dm →
    ∀ b δ : ℝ, 0 < b → b < 1 → 0 < δ →
    ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ μ ∈ Kset, ∀ l r : ℝ, 0 < l → l < r → r ≤ Real.exp (δ / 2) * l → r ≤ p.ε ^ (-b) →
      ∀ g : Chart → Ten3, IsBoxTensor g →
        (∀ x, g x ≠ 0 → Real.exp δ * l ≤ x.1 ∧ x.1 < Real.exp δ * r) →
        AEStronglyMeasurable ((ageBand l r).indicator
              (farOut p.R p.c p.ν μ δ (p.ε ^ (-b)) g)) (ageμ p.c (-3 / 2)) ∧
          eLpNorm ((ageBand l r).indicator (farOut p.R p.c p.ν μ δ (p.ε ^ (-b)) g)) 2
              (ageμ p.c (-3 / 2)) ≤
            ENNReal.ofReal (C * p.ν⁻¹ ^ k * (p.ε * Real.sqrt r)) *
              eLpNorm g 2 (ageμ p.c (-1 / 2))

theorem isBoxTensor_truncAbove (T : ℝ) {f : Chart → Ten3} (hf : IsBoxTensor f) :
    IsBoxTensor (truncAbove T f) := by
  obtain ⟨B, hB⟩ := hf.bounded
  obtain ⟨s₁, s₂, L, hs, hband⟩ := hf.band
  refine ⟨?_, ⟨B, fun p => ?_⟩, ⟨s₁, s₂, L, hs, fun p hp => ?_⟩⟩
  · unfold truncAbove
    exact Measurable.ite (measurableSet_lt measurable_fst measurable_const) hf.measurable
      measurable_const
  · unfold truncAbove
    split_ifs
    · exact hB p
    · simpa using (norm_nonneg (f p)).trans (hB p)
  · unfold truncAbove at hp
    split_ifs at hp with h
    · exact hband p hp
    · exact absurd rfl hp

theorem norm_truncAbove_le (T : ℝ) (f : Chart → Ten3) (p : Chart) :
    ‖truncAbove T f p‖ ≤ ‖f p‖ := by
  unfold truncAbove
  split_ifs <;> simp

/-- **`stripKernelBound_of_parts`** (source 3996-4005). -/
theorem stripKernelBound_of_parts (hSp : StripSplit) (hN : StripNear) (hF : StripFar) :
    StripKernelBound := by
  intro Kset hK hKs dm dp hdm b δ hb hb1 hδ
  obtain ⟨C1, k1, ν1, hν1, h1⟩ := hN Kset hK hKs dm dp hdm b δ hb hb1 hδ
  obtain ⟨C2, k2, ν2, hν2, h2⟩ := hF Kset hK hKs dm dp hdm b δ hb hb1 hδ
  refine ⟨max C1 0 + max C2 0, max k1 k2, min (min ν1 ν2) 1, by positivity, ?_⟩
  intro p d hreg hν μ hμ l r hl hlr hrl hrS f hf hsupp
  have hνpos := p.ν_pos
  have hεpos := p.ε_pos
  have hν1' : p.ν ≤ ν1 := (hν.trans (min_le_left _ _)).trans (min_le_left _ _)
  have hν2' : p.ν ≤ ν2 := (hν.trans (min_le_left _ _)).trans (min_le_right _ _)
  have hν3 : p.ν ≤ 1 := hν.trans (min_le_right _ _)
  set g := truncAbove (Real.exp δ * r) f with hg
  have hgbox : IsBoxTensor g := isBoxTensor_truncAbove _ hf
  have hgsupp : ∀ x, g x ≠ 0 → Real.exp δ * l ≤ x.1 ∧ x.1 < Real.exp δ * r := by
    intro x hx
    have hx' := hx
    simp only [hg, truncAbove] at hx'
    split_ifs at hx' with h
    · exact ⟨hsupp x hx', h⟩
    · exact absurd rfl hx'
  have hRpos : 0 < p.R := by
    have : p.R = p.ε⁻¹ := by simp [Params.R]
    rw [this]; positivity
  obtain ⟨hm1, hb1'⟩ := h1 p d hreg hν1' μ hμ l r hl hlr hrl hrS g hgbox hgsupp
  obtain ⟨hm2, hb2'⟩ := h2 p d hreg hν2' μ hμ l r hl hlr hrl hrS g hgbox hgsupp
  have hfun : (ageBand l r).indicator
      (fullOut p.R p.c p.ν μ f - farOut p.R p.c p.ν μ δ (p.ε ^ (-b)) f) =
      (ageBand l r).indicator (fullOut p.R p.c p.ν μ g) -
        (ageBand l r).indicator (farOut p.R p.c p.ν μ δ (p.ε ^ (-b)) g) := by
    rw [← Set.indicator_sub']
    funext x
    by_cases hx : x ∈ ageBand l r
    · simp only [Set.indicator_of_mem hx, Pi.sub_apply]
      exact hSp p.R p.c p.ν μ δ (p.ε ^ (-b)) l r hRpos p.c_pos hνpos
        (hKs hμ) hδ hl hlr hrl hrS f hf hsupp x hx
    · simp [Set.indicator_of_notMem hx]
  rw [hfun]
  refine (eLpNorm_sub_le hm1 hm2 (by norm_num)).trans ?_
  have hgf : eLpNorm g 2 (ageμ p.c (-1 / 2)) ≤ eLpNorm f 2 (ageμ p.c (-1 / 2)) :=
    eLpNorm_mono (fun x => norm_truncAbove_le _ f x)
  have hE : 0 ≤ p.ε * Real.sqrt r := by positivity
  have hνinv : 1 ≤ p.ν⁻¹ := by
    rw [one_le_inv₀ hνpos]; exact hν3
  have hpow1 : p.ν⁻¹ ^ k1 ≤ p.ν⁻¹ ^ (max k1 k2) := pow_le_pow_right₀ hνinv (le_max_left _ _)
  have hpow2 : p.ν⁻¹ ^ k2 ≤ p.ν⁻¹ ^ (max k1 k2) := pow_le_pow_right₀ hνinv (le_max_right _ _)
  have hP : 0 ≤ p.ν⁻¹ ^ (max k1 k2) * (p.ε * Real.sqrt r) := by positivity
  have hP1 : 0 ≤ p.ν⁻¹ ^ k1 * (p.ε * Real.sqrt r) := by positivity
  have hP2 : 0 ≤ p.ν⁻¹ ^ k2 * (p.ε * Real.sqrt r) := by positivity
  have e1 : C1 * p.ν⁻¹ ^ k1 * (p.ε * Real.sqrt r) ≤
      max C1 0 * (p.ν⁻¹ ^ (max k1 k2) * (p.ε * Real.sqrt r)) := by
    rw [mul_assoc]
    exact mul_le_mul (le_max_left _ _) (mul_le_mul_of_nonneg_right hpow1 hE) hP1
      (le_max_right _ _)
  have e2 : C2 * p.ν⁻¹ ^ k2 * (p.ε * Real.sqrt r) ≤
      max C2 0 * (p.ν⁻¹ ^ (max k1 k2) * (p.ε * Real.sqrt r)) := by
    rw [mul_assoc]
    exact mul_le_mul (le_max_left _ _) (mul_le_mul_of_nonneg_right hpow2 hE) hP2
      (le_max_right _ _)
  calc _ ≤ ENNReal.ofReal (max C1 0 * (p.ν⁻¹ ^ (max k1 k2) * (p.ε * Real.sqrt r))) *
        eLpNorm f 2 (ageμ p.c (-1 / 2)) +
      ENNReal.ofReal (max C2 0 * (p.ν⁻¹ ^ (max k1 k2) * (p.ε * Real.sqrt r))) *
        eLpNorm f 2 (ageμ p.c (-1 / 2)) := by
        refine add_le_add ?_ ?_
        · exact hb1'.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal e1) hgf)
        · exact hb2'.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal e2) hgf)
    _ = _ := by
        rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 2
        ring
