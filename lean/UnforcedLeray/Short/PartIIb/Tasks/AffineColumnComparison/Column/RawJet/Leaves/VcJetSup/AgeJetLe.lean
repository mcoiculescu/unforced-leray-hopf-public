import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_6_1_5
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.VcJetSup.SpatialJetBound
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.VcJetSup.AgeJetLe.LapJet
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.Column.RawJet.Leaves.VcJetSup.AgeJetLe.Uncurried

/-!
Task `PartII-b:G4/3/6/1/5/1`.  `VcAgeJetLe` (SP 2205): by the vector heat equation `Train.Vc_heat`
and the commutation of `∂_s` with the spatial Laplacian for the jointly smooth `Vc`
(`VcSmooth`, symmetry of second derivatives, `Uncurried.lean`), for `s > 0`
`∂_s^ℓ Vc = ν^ℓ Δ^ℓ Vc` (`iteratedDeriv_Vc`); then `Δ^ℓ` costs `2ℓ` spatial derivatives with
constant `2^ℓ` (`norm_jet_lapD_iterate_le`, `LapJet.lean`).
-/

set_option autoImplicit false

open Set
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Train UnforcedLeray.Cyl UnforcedLeray.Short.PartI

theorem slice_Dv {F : ℝ × Plane → Vec} (hF : Sm F) {t : ℝ} (ht : 0 < t) (e : Plane) :
    Dv e (fun w => F (t, w)) = fun w => Dx (0, e) F (t, w) := by
  funext w
  have h1 : HasFDerivAt (fun w : Plane => (t, w)) (ContinuousLinearMap.inr ℝ ℝ Plane) w :=
    hasFDerivAt_prodMk_right t w
  have h2 := (hF.diffAt (mem_UU ht)).hasFDerivAt.comp w h1
  show fderiv ℝ (F ∘ fun w : Plane => (t, w)) w e = fderiv ℝ F (t, w) (0, e)
  rw [h2.fderiv]
  rfl

theorem slice_lapD {F : ℝ × Plane → Vec} (hF : Sm F) {t : ℝ} (ht : 0 < t) :
    lapD (fun w => F (t, w)) = fun w => LapU F (t, w) := by
  funext z
  show Dv ((1 : ℝ), (0 : ℝ)) (Dv ((1 : ℝ), (0 : ℝ)) (fun w => F (t, w))) z +
    Dv ((0 : ℝ), (1 : ℝ)) (Dv ((0 : ℝ), (1 : ℝ)) (fun w => F (t, w))) z = _
  have a1 : Dv ((1 : ℝ), (0 : ℝ)) (fun w => F (t, w)) = fun w => Dx eQ F (t, w) :=
    slice_Dv hF ht _
  have a2 : Dv ((0 : ℝ), (1 : ℝ)) (fun w => F (t, w)) = fun w => Dx eE F (t, w) :=
    slice_Dv hF ht _
  have b1 : Dv ((1 : ℝ), (0 : ℝ)) (fun w => Dx eQ F (t, w)) = fun w => Dx eQ (Dx eQ F) (t, w) :=
    slice_Dv (hF.dx eQ) ht _
  have b2 : Dv ((0 : ℝ), (1 : ℝ)) (fun w => Dx eE F (t, w)) = fun w => Dx eE (Dx eE F) (t, w) :=
    slice_Dv (hF.dx eE) ht _
  rw [a1, a2, b1, b2]
  rfl

theorem hasDerivAt_slice {F : ℝ × Plane → Vec} (hF : Sm F) {t : ℝ} (ht : 0 < t) (w : Plane) :
    HasDerivAt (fun r => F (r, w)) (Dx eT F (t, w)) t := by
  have h0 : HasDerivAt (fun r : ℝ => (r, w)) ((1 : ℝ), (0 : Plane)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t w)
  exact (hF.diffAt (mem_UU ht)).hasFDerivAt.comp_hasDerivAt t h0

section Heat

variable {ν c : ℝ}

/-- `Vc` as a function of `(s, z)`. -/
noncomputable def G0 (ν c : ℝ) : ℝ × Plane → Vec := fun x => Vc ν c x.1 x.2

theorem sm_G0 (hν : 0 < ν) (hc : 0 < c) : Sm (G0 ν c) := vcSmooth_proof ν c hν hc

/-- The iterated Laplacians of `Vc`, as functions of `(s, z)`. -/
noncomputable def Gl (ν c : ℝ) (ℓ : ℕ) : ℝ × Plane → Vec := LapU^[ℓ] (G0 ν c)

theorem Gl_succ (ν c : ℝ) (ℓ : ℕ) : Gl ν c (ℓ + 1) = LapU (Gl ν c ℓ) := by
  unfold Gl
  rw [Function.iterate_succ_apply']

theorem Gl_zero (ν c : ℝ) : Gl ν c 0 = G0 ν c := rfl

theorem Gl_spec (hν : 0 < ν) (hc : 0 < c) :
    ∀ ℓ : ℕ, Sm (Gl ν c ℓ) ∧ EqOn (Dx eT (Gl ν c ℓ)) (fun y => ν • Gl ν c (ℓ + 1) y) UU := by
  intro ℓ
  induction ℓ with
  | zero =>
    refine ⟨sm_G0 hν hc, ?_⟩
    rintro ⟨t, w⟩ hx
    have ht : 0 < t := hx.1
    have h1 : Dx eT (Gl ν c 0) (t, w) = deriv (fun r => Vc ν c r w) t :=
      (hasDerivAt_slice (sm_G0 hν hc) ht w).deriv.symm
    have h2 := (Vc_heat hν hc.ne' ht.le w).deriv
    rw [h1, h2, vecLaplacian_eq_lapD (vc_contDiff_space hν hc ht.le)]
    have h3 := congrFun (slice_lapD (sm_G0 hν hc) ht) w
    show _ = ν • LapU (G0 ν c) (t, w)
    rw [← h3]
    rfl
  | succ ℓ ih =>
    obtain ⟨hs, he⟩ := ih
    have hs' : Sm (Gl ν c (ℓ + 1)) := by rw [Gl_succ]; exact hs.lap
    refine ⟨hs', ?_⟩
    intro x hx
    have step1 : Dx eT (Gl ν c (ℓ + 1)) x = LapU (Dx eT (Gl ν c ℓ)) x := by
      rw [Gl_succ]; exact LapU_comm_t hs hx
    have step2 := LapU_congr he hx
    have step3 := LapU_smul hs' ν hx
    rw [step1, step2, step3, Gl_succ ν c (ℓ + 1)]

theorem Gl_slice (hν : 0 < ν) (hc : 0 < c) {t : ℝ} (ht : 0 < t) :
    ∀ ℓ : ℕ, (fun w => Gl ν c ℓ (t, w)) = lapD^[ℓ] (Vc ν c t) := by
  intro ℓ
  induction ℓ with
  | zero => rfl
  | succ ℓ ih =>
    rw [Gl_succ, Function.iterate_succ_apply', ← ih]
    exact (slice_lapD (Gl_spec hν hc ℓ).1 ht).symm

/-- **Age derivatives through the heat equation**: for `s > 0`, `∂_s^ℓ Vc = ν^ℓ Δ^ℓ Vc`. -/
theorem iteratedDeriv_Vc (hν : 0 < ν) (hc : 0 < c) :
    ∀ ℓ : ℕ, ∀ t : ℝ, 0 < t → ∀ w : Plane,
      iteratedDeriv ℓ (fun r => Vc ν c r w) t = ν ^ ℓ • Gl ν c ℓ (t, w) := by
  intro ℓ
  induction ℓ with
  | zero => intro t ht w; simp [Gl_zero, G0]
  | succ ℓ ih =>
    intro t ht w
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv ℓ (fun r => Vc ν c r w) =ᶠ[nhds t]
        fun r => ν ^ ℓ • Gl ν c ℓ (r, w) := by
      filter_upwards [Ioi_mem_nhds ht] with r hr using ih r hr w
    rw [hev.deriv_eq]
    obtain ⟨hs, he⟩ := Gl_spec hν hc ℓ
    have hd : HasDerivAt (fun r => ν ^ ℓ • Gl ν c ℓ (r, w))
        (ν ^ ℓ • Dx eT (Gl ν c ℓ) (t, w)) t := (hasDerivAt_slice hs ht w).const_smul (ν ^ ℓ)
    rw [hd.deriv, he (mem_UU ht), smul_smul, pow_succ]

end Heat

theorem vcAgeJetLe_proof : UnforcedLeray.Short.IIb.VcAgeJetLe := by
  intro ℓ j
  refine ⟨2 ^ ℓ, by positivity, ?_⟩
  intro ν c hν hc s hs z
  have hsm := vc_contDiff_space hν hc hs.le
  have hfun : (fun z' => iteratedDeriv ℓ (fun r => Vc ν c r z') s) =
      fun z' => ν ^ ℓ • (lapD^[ℓ] (Vc ν c s)) z' := by
    funext w
    rw [iteratedDeriv_Vc hν hc ℓ s hs w]
    rw [← Gl_slice hν hc hs ℓ]
  have hL : ContDiffAt ℝ j (lapD^[ℓ] (Vc ν c s)) z :=
    ((contDiff_lapD_iterate hsm ℓ).of_le (by exact_mod_cast le_top)).contDiffAt
  have e : ageJet ℓ j (fun r w => Vc ν c r w) s z =
      ν ^ ℓ • iteratedFDeriv ℝ j (lapD^[ℓ] (Vc ν c s)) z := by
    show iteratedFDeriv ℝ j (fun z' => iteratedDeriv ℓ (fun r => Vc ν c r z') s) z = _
    rw [hfun]
    exact iteratedFDeriv_const_smul_apply' hL
  rw [e, norm_smul, Real.norm_of_nonneg (by positivity)]
  have := norm_jet_lapD_iterate_le hsm ℓ j z
  calc ν ^ ℓ * ‖iteratedFDeriv ℝ j (lapD^[ℓ] (Vc ν c s)) z‖
      ≤ ν ^ ℓ * (2 ^ ℓ * ‖iteratedFDeriv ℝ (j + 2 * ℓ) (Vc ν c s) z‖) := by gcongr
    _ = ν ^ ℓ * 2 ^ ℓ * ‖jet (j + 2 * ℓ) (Vc ν c s) z‖ := by
      rw [mul_assoc]; rfl

end UnforcedLeray.Short.IIb
