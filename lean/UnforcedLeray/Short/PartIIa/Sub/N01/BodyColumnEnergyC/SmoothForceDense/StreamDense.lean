import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_1
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.SmoothForceDense.StreamSolenoidal
import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_9_1_1_3
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.SmoothForceDense.StreamDense.SliceL2
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.SmoothForceDense.StreamDense.ProdTestOrth
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.SmoothForceDense.StreamDense.CylDense
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.SmoothForceDense.StreamDense.LimitStep
import UnforcedLeray.Short.PartIIa.Sub.N01.BodyColumnEnergyC.SmoothForceDense.StreamDense.SliceVanish

/-!


Source of record: `the November 2 reference manuscript`, lines 1684-1689.

Status: this file proves the Hilbert-space reduction `streamDense_of`:
`StreamDense` follows from `StreamOrthCore`, the statement that a solenoidal element of `𝓗`
orthogonal to all stream fields vanishes. It also proves that `StreamSet c` is closed under
addition and scalar multiplication (`sdn_streamSet_add`, `sdn_streamSet_smul`).
The core `StreamOrthCore` is NOT proved here (it needs the slice-by-slice div-curl uniqueness on the
`(q,η)` cylinder, see the report).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIa.N01

open UnforcedLeray.B0220 (Profile HSpace measureH)
open UnforcedLeray.B0223 (MeridC)

/-- Orthogonal core: a solenoidal element of `𝓗` orthogonal to every stream field vanishes. -/
def StreamOrthCore : Prop :=
  ∀ c : ℝ, 0 < c → ∀ h ∈ solenoidalHC 0 c, (∀ g ∈ StreamSet c, inner ℂ g h = 0) → h = 0

theorem sdn_isStreamFn_add {c : ℝ} {ψ₁ ψ₂ : Profile → ℂ} (h₁ : IsStreamFn c ψ₁)
    (h₂ : IsStreamFn c ψ₂) : IsStreamFn c (ψ₁ + ψ₂) := by
  obtain ⟨hs1, hp1, a1, b1, R1, ha1, hz1⟩ := h₁
  obtain ⟨hs2, hp2, a2, b2, R2, ha2, hz2⟩ := h₂
  refine ⟨hs1.add hs2, fun p => ?_, min a1 a2, max b1 b2, max R1 R2, lt_min ha1 ha2,
    fun p hp => ?_⟩
  · show ψ₁ _ + ψ₂ _ = ψ₁ p + ψ₂ p
    rw [hp1 p, hp2 p]
  · have e1 : ψ₁ p = 0 := by
      apply hz1 p
      rcases hp with h | h | h
      · exact Or.inl (lt_of_lt_of_le h (min_le_left a1 a2))
      · exact Or.inr (Or.inl (lt_of_le_of_lt (le_max_left b1 b2) h))
      · exact Or.inr (Or.inr (lt_of_le_of_lt (le_max_left R1 R2) h))
    have e2 : ψ₂ p = 0 := by
      apply hz2 p
      rcases hp with h | h | h
      · exact Or.inl (lt_of_lt_of_le h (min_le_right a1 a2))
      · exact Or.inr (Or.inl (lt_of_le_of_lt (le_max_right b1 b2) h))
      · exact Or.inr (Or.inr (lt_of_le_of_lt (le_max_right R1 R2) h))
    show ψ₁ p + ψ₂ p = 0
    rw [e1, e2, add_zero]

theorem sdn_isStreamFn_smul {c : ℝ} {ψ : Profile → ℂ} (a : ℂ) (h : IsStreamFn c ψ) :
    IsStreamFn c (a • ψ) := by
  obtain ⟨hs, hp, s1, s2, R, hs1, hz⟩ := h
  refine ⟨hs.const_smul a, fun p => ?_, s1, s2, R, hs1, fun p hp' => ?_⟩
  · show a • ψ _ = a • ψ p
    rw [hp p]
  · show a • ψ p = 0
    rw [hz p hp', smul_zero]

theorem sdn_fderiv_add {ψ₁ ψ₂ : Profile → ℂ} (h₁ : ContDiff ℝ ∞ ψ₁) (h₂ : ContDiff ℝ ∞ ψ₂)
    (p : Profile) (v : Profile) :
    fderiv ℝ (ψ₁ + ψ₂) p v = fderiv ℝ ψ₁ p v + fderiv ℝ ψ₂ p v := by
  have d1 := h₁.differentiable (by simp)
  have d2 := h₂.differentiable (by simp)
  rw [fderiv_add (d1 p) (d2 p)]
  rfl

theorem sdn_fderiv_smul (a : ℂ) {ψ : Profile → ℂ} (h₁ : ContDiff ℝ ∞ ψ) (p : Profile)
    (v : Profile) : fderiv ℝ (a • ψ) p v = a • fderiv ℝ ψ p v := by
  have d1 := h₁.differentiable (by simp)
  rw [fderiv_const_smul (d1 p)]
  rfl

/-- `StreamField` is additive on smooth stream functions. -/
theorem sdn_streamField_add {ψ₁ ψ₂ : Profile → ℂ} (h₁ : ContDiff ℝ ∞ ψ₁)
    (h₂ : ContDiff ℝ ∞ ψ₂) (p : Profile) :
    StreamField (ψ₁ + ψ₂) p = StreamField ψ₁ p + StreamField ψ₂ p := by
  have e1 : pdEta (ψ₁ + ψ₂) p = pdEta ψ₁ p + pdEta ψ₂ p := sdn_fderiv_add h₁ h₂ p _
  have e2 : pdQ (ψ₁ + ψ₂) p = pdQ ψ₁ p + pdQ ψ₂ p := sdn_fderiv_add h₁ h₂ p _
  ext i
  fin_cases i
  · simp [StreamField, e1]
  · simp [StreamField, e2]
    ring

theorem sdn_streamField_smul (a : ℂ) {ψ : Profile → ℂ} (h₁ : ContDiff ℝ ∞ ψ) (p : Profile) :
    StreamField (a • ψ) p = a • StreamField ψ p := by
  have e1 : pdEta (a • ψ) p = a • pdEta ψ p := sdn_fderiv_smul a h₁ p _
  have e2 : pdQ (a • ψ) p = a • pdQ ψ p := sdn_fderiv_smul a h₁ p _
  ext i
  fin_cases i
  · simp [StreamField, e1]
  · simp [StreamField, e2]

theorem sdn_zero_mem (c : ℝ) : (0 : HSpace c MeridC) ∈ StreamSet c := by
  refine ⟨0, ⟨contDiff_zero_fun, fun p => rfl, 1, 1, 0, one_pos, fun p _ => rfl⟩, ?_⟩
  filter_upwards [Lp.coeFn_zero MeridC 2 (measureH c)] with p hp
  rw [hp, Pi.zero_apply]
  ext i
  fin_cases i <;> simp [StreamField, pdEta, pdQ]

theorem sdn_streamSet_add {c : ℝ} {g₁ g₂ : HSpace c MeridC} (h₁ : g₁ ∈ StreamSet c)
    (h₂ : g₂ ∈ StreamSet c) : g₁ + g₂ ∈ StreamSet c := by
  obtain ⟨ψ₁, hψ₁, e₁⟩ := h₁
  obtain ⟨ψ₂, hψ₂, e₂⟩ := h₂
  refine ⟨ψ₁ + ψ₂, sdn_isStreamFn_add hψ₁ hψ₂, ?_⟩
  filter_upwards [Lp.coeFn_add g₁ g₂, e₁, e₂] with p hA hB hC
  rw [hA, Pi.add_apply, hB, hC, sdn_streamField_add hψ₁.1 hψ₂.1 p]

theorem sdn_streamSet_smul {c : ℝ} (a : ℂ) {g : HSpace c MeridC} (h : g ∈ StreamSet c) :
    a • g ∈ StreamSet c := by
  obtain ⟨ψ, hψ, e⟩ := h
  refine ⟨a • ψ, sdn_isStreamFn_smul a hψ, ?_⟩
  filter_upwards [Lp.coeFn_smul a g, e] with p hA hB
  rw [hA, Pi.smul_apply, hB, sdn_streamField_smul a hψ.1 p]

/-- Reduction: `StreamDense` follows from the orthogonal core. -/
theorem streamDense_of (hcore : StreamOrthCore) : StreamDense := by
  intro c hc g hg
  let K : Submodule ℂ (HSpace c MeridC) :=
    { carrier := StreamSet c
      add_mem' := fun h₁ h₂ => sdn_streamSet_add h₁ h₂
      zero_mem' := sdn_zero_mem c
      smul_mem' := fun a _ hx => sdn_streamSet_smul a hx }
  have hKc : (K : Set (HSpace c MeridC)) = StreamSet c := rfl
  have hgK : g ∈ Kᗮᗮ := by
    rw [Submodule.mem_orthogonal]
    intro h hh
    have hperp : ∀ u ∈ StreamSet c,
        inner ℂ u ((solenoidalHC 0 c).starProjection h) = 0 := by
      intro u hu
      have huS : u ∈ solenoidalHC 0 c := streamSolenoidal c hc u hu
      rw [← Submodule.inner_starProjection_left_eq_right,
        (Submodule.starProjection_eq_self_iff).2 huS]
      exact (Submodule.mem_orthogonal K h).1 hh u hu
    have hh0 : (solenoidalHC 0 c).starProjection h = 0 :=
      hcore c hc _ (Submodule.starProjection_apply_mem _ _) hperp
    have hPg : (solenoidalHC 0 c).starProjection g = g :=
      (Submodule.starProjection_eq_self_iff).2 hg
    calc inner ℂ h g = inner ℂ h ((solenoidalHC 0 c).starProjection g) := by rw [hPg]
      _ = inner ℂ ((solenoidalHC 0 c).starProjection h) g :=
          (Submodule.inner_starProjection_left_eq_right (solenoidalHC 0 c) h g).symm
      _ = 0 := by rw [hh0, inner_zero_left]
  have hcl : g ∈ (K.topologicalClosure : Set (HSpace c MeridC)) := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure]
    exact hgK
  rw [Submodule.topologicalClosure_coe, hKc] at hcl
  exact hcl

/-- The stream fields are dense in the solenoidal subspace of `𝓗` (source lines 1684-1689). -/
theorem streamDense : UnforcedLeray.Short.PartIIa.N01.StreamDense :=
  streamDense_of (fun c hc h hs ho =>
    Sub.streamOrthCore_of Sub.sliceL2 Sub.prodTestOrth Sub.cylDense Sub.limitStep Sub.sliceVanish
      c hc h hs ho)

end UnforcedLeray.Short.PartIIa.N01
