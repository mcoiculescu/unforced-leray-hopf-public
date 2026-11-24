import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Lemmas

/-!
# Decomposition of `compactWindowBlock_of` (item `PartIII-b:C/near/delta/8`)

Source of record `the November 2 reference manuscript`,
paragraph 3956-3994 (complete blocks).  The block `g⁻¹1_{bin}(S_N - S₀)1_{t<e^δ l}g` is handled by

* `FarMaskVanish` (3905-3916): `S_far` only sees inputs with `t > e^δ s`, so `1_{bin} S_far
  1_{t<e^δ l} = 0` for `l > 0`;
* `CompactWindowComparison` (3956-3967, `PartIIa.NearCompactFreeComparison` in real form, with
  `S₀` identified with the real form of the flat stress map by uniqueness of the causal solution):
  the un-conjugated block `1_{bin}(S_ε - S₀)1_{t<e^δ l}` has norm `≤ C ν^{-k} ε^{1/50-K(a+b)}`;
* `GainBlockRatio` (3978-3990, `GainRatioSup`, `GainRatioTanh`): the gain costs at most
  `e^{η_δ/ν}` on a block with output age `≥ l` and input age `< e^δ l`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Cons.C03.Concrete
  UnforcedLeray.Blueprint.Planar

/-- **The far mask misses the complete block** (source 3905-3916).  If `Sf` is the far mask
(`IsFarMask`), then for `l > 0` the block with output in `{s ≥ l}` (any bin) and input in
`{t < e^δ l}` vanishes: `1_{bin} S_far 1_{t<e^δ l} = 0`.  (Pointwise on the dense box class
`IsBoxTensor` the kernel only sees `t > e^δ s ≥ e^δ l`; extend by continuity.)  The spaces are the nondegenerate ones `0 < c`, `0 ≤ m_Z`, `0 < ρ_b`
of the source. -/
def FarMaskVanish : Prop :=
  ∀ (c mZ ρb R ν μ δ S : ℝ), 0 < c → 0 ≤ mZ → 0 < ρb → ∀ (Sf : Zsp c mZ ρb →L[ℝ] Hsp c),
    IsFarMask R ν μ δ S Sf →
    ∀ l r L : ℝ, 0 < l → 0 ≤ δ →
      outRestr c (binSet l r L) ∘L Sf ∘L inRestr c mZ ρb (ageBelow (Real.exp δ * l)) = 0

/-- **The compact-output comparison on the complete block** (source 3956-3967, with the choice
of the cutoff `χ = 1` on the bin box, `Γ^K ≤ P_ν ε^{-K(a+b)}`, and `S₀` identified with the real
form of the `PartIIa` flat stress map via `PartIIa.NearStressMapExists` and uniqueness of the
causal solution).  There is `K` (chosen before `a, b`) such that at every level of the regime with
`ν ≤ ν₀`, for the real form `Seps` of a curved stress map and the free `S₀`, every bin
`[l, r) × {|η| ≤ L_⊥}` with `ε^a ≤ l < r ≤ e^{δ/2} l`, `r ≤ ε^{-b}`:
`‖1_{bin}(S_ε - S₀)1_{t<e^δ l}‖_{Z→H} ≤ C ν^{-k} ε^{1/50-K(a+b)}`. -/
def CompactWindowComparison : Prop :=
  ∀ Kset : Set ℝ, IsCompact Kset → Kset ⊆ Ioo 0 (1 / 4) → ∀ mZ : ℝ, 0 ≤ mZ →
    ∀ dm dp : ℝ, 0 < dm →
    ∃ K : ℕ, ∀ a b δ Cperp : ℝ, 0 < a → 0 < b → b < 1 → 0 < δ →
    ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ ρb : ℝ, 0 < ρb → ρb ≤ 1 → ∀ μ ∈ Kset,
      ∀ (Seps S0 : Zsp p.c mZ ρb →L[ℝ] Hsp p.c)
        (Seps' : UnforcedLeray.Short.PartIIa.HTSpace p.c →L[ℂ]
          UnforcedLeray.B0220.HSpace p.c UnforcedLeray.B0223.MeridC),
        UnforcedLeray.Short.PartIIa.IsStressMap p.c p.ε
            (UnforcedLeray.Short.PartIIa.Teps (P := p.period) p.ν_pos p.ε_pos p.c_pos rfl (μ : ℂ))
            Seps' →
          IsStressTransport Seps Seps' → IsFreeStress S0 p.ν μ →
        ∀ l r : ℝ, p.ε ^ a ≤ l → l < r → r ≤ Real.exp (δ / 2) * l → r ≤ p.ε ^ (-b) →
          ‖outRestr p.c (binSet l r (transL Cperp p.c p.ν (p.ε ^ (-b)))) ∘L (Seps - S0) ∘L
              inRestr p.c mZ ρb (ageBelow (Real.exp δ * l))‖ ≤
            C * p.ν⁻¹ ^ k * p.ε ^ (1 / 50 - (K : ℝ) * (a + b))

/-- **The gain ratio on a complete block** (source 3978-3990 with `GainRatioSup`,
`GainRatioTanh`, `η_δ = γ tanh(3δ/8)`): for `γ ≥ 0`, output region inside `{s ≥ l}` and input
region inside `{t < e^δ l}`, `‖g⁻¹ 1_A X 1_B g‖ ≤ e^{η_δ/ν}‖1_A X 1_B‖`. -/
def GainBlockRatio : Prop :=
  ∀ (c mZ ρb γ ν δ l : ℝ) (hν : 0 < ν), 0 ≤ γ → 0 < δ → 0 < l →
    ∀ A B : Set Chart, A ⊆ ageAbove l → B ⊆ ageBelow (Real.exp δ * l) →
      ∀ X : Zsp c mZ ρb →L[ℝ] Hsp c,
        ‖gainBlockS γ hν A B X‖ ≤
          Real.exp (etaDelta γ δ / ν) * ‖outRestr c A ∘L X ∘L inRestr c mZ ρb B‖

theorem binSet_subset_ageAbove (l r L : ℝ) : binSet l r L ⊆ ageAbove l := fun _ h => h.1

/-- The complete block, from the three lemmas. -/
theorem compactWindowBlock_of (h1 : FarMaskVanish) (h2 : CompactWindowComparison)
    (h3 : GainBlockRatio) : CompactWindowBlock := by
  intro P hP Kset hK hKs mZ hmZ dm dp hdm
  obtain ⟨K, hK'⟩ := h2 Kset hK hKs mZ hmZ dm dp hdm
  refine ⟨K, ?_⟩
  intro a b δ Cperp ha hb hb1 hδ
  obtain ⟨C, k, ν₀, hν₀, hmain⟩ := hK' a b δ Cperp ha hb hb1 hδ
  refine ⟨C, k, ν₀, hν₀, ?_⟩
  intro p d hreg hν ρb hρ hρ1 μ hμ SN S0 hSN hS0 l r hal hlr hr hrS
  obtain ⟨Seps, Sf, Seps', hSeps, htr, hfar, rfl⟩ := hSN
  have hlpos : 0 < l := lt_of_lt_of_le (Real.rpow_pos_of_pos p.ε_pos a) hal
  have hγ : 0 ≤ P.eigenvalue.re := hP.eigenpair.re_pos.le
  have hz := h3 p.c mZ ρb P.eigenvalue.re p.ν δ l p.ν_pos hγ hδ hlpos
    (binSet l r (transL Cperp p.c p.ν (p.ε ^ (-b)))) (ageBelow (Real.exp δ * l))
    (binSet_subset_ageAbove _ _ _) (fun _ h => h) (Seps - Sf - S0)
  have hsplit : outRestr p.c (binSet l r (transL Cperp p.c p.ν (p.ε ^ (-b)))) ∘L
        (Seps - Sf - S0) ∘L inRestr p.c mZ ρb (ageBelow (Real.exp δ * l)) =
      outRestr p.c (binSet l r (transL Cperp p.c p.ν (p.ε ^ (-b)))) ∘L (Seps - S0) ∘L
        inRestr p.c mZ ρb (ageBelow (Real.exp δ * l)) := by
    have h0 := h1 p.c mZ ρb p.R p.ν μ δ (p.ε ^ (-b)) p.c_pos hmZ hρ Sf hfar l r
      (transL Cperp p.c p.ν (p.ε ^ (-b))) hlpos hδ.le
    have e : (Seps - Sf - S0) = (Seps - S0) - Sf := by abel
    rw [e]
    ext F
    have h0F := congrArg (fun T => T F) h0
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.zero_apply] at h0F ⊢
    rw [map_sub, h0F]; simp
  rw [hsplit] at hz
  have hm := hmain p d hreg hν ρb hρ hρ1 μ hμ Seps S0 Seps' hSeps htr hS0 l r hal hlr hr hrS
  have hexp : 0 ≤ Real.exp (etaDelta P.eigenvalue.re δ / p.ν) := (Real.exp_pos _).le
  calc _ ≤ _ := hz
    _ ≤ Real.exp (etaDelta P.eigenvalue.re δ / p.ν) *
          (C * p.ν⁻¹ ^ k * p.ε ^ (1 / 50 - (K : ℝ) * (a + b))) :=
        mul_le_mul_of_nonneg_left hm hexp
    _ = _ := by ring
end UnforcedLeray.Short.PartIIIb.NearInst.Delta
