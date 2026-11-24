import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G2_1_org
import UnforcedLeray.Short.PartIIb.Tasks.RieszThorinApplication.HrOperatorFamily.Linearity

/-!
# `PartII-b:G2/1/org/D`: `PhysRespReal`

Source: `the November 2 reference manuscript` lines 1665-1672.  The response equation
has real coefficients; conjugation maps responses of a real source to responses of the same source.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open HrOpHelp

namespace RespRealD

/-- Coordinatewise complex conjugation on `ℂ³`. -/
def cj (v : CVec3) : CVec3 := WithLp.toLp 2 fun i => starRingEnd ℂ (v i)

theorem cj_apply (v : CVec3) (i : Fin 3) : cj v i = starRingEnd ℂ (v i) := rfl

theorem cj_cj (v : CVec3) : cj (cj v) = v := by
  ext i; simp [cj_apply]

theorem cj_add (u v : CVec3) : cj (u + v) = cj u + cj v := by
  ext i; simp [cj_apply]

theorem cj_sub (u v : CVec3) : cj (u - v) = cj u - cj v := by
  ext i; simp [cj_apply]

theorem cj_neg (v : CVec3) : cj (-v) = - cj v := by
  ext i; simp [cj_apply]

theorem cj_smul (a : ℂ) (v : CVec3) : cj (a • v) = starRingEnd ℂ a • cj v := by
  ext i; simp [cj_apply]

theorem cj_smul_real (r : ℝ) (v : CVec3) : cj (r • v) = r • cj v := by
  ext i; simp [cj_apply]

theorem cj_sum {ι : Type*} (s : Finset ι) (f : ι → CVec3) : cj (∑ i ∈ s, f i) = ∑ i ∈ s, cj (f i) := by
  ext i; simp [cj_apply, Finset.sum_apply]

theorem norm_cj (v : CVec3) : ‖cj v‖ = ‖v‖ := by
  simp [EuclideanSpace.norm_eq, cj_apply]

theorem isometry_cj : Isometry cj :=
  Isometry.of_dist_eq fun u v => by rw [dist_eq_norm, dist_eq_norm, ← cj_sub, norm_cj]

/-- Conjugation as a real continuous linear equivalence of `ℂ³`. -/
def starE : CVec3 ≃L[ℝ] CVec3 :=
  { toFun := cj
    invFun := cj
    map_add' := cj_add
    map_smul' := fun r v => by simpa using cj_smul_real r v
    left_inv := cj_cj
    right_inv := cj_cj
    continuous_toFun := isometry_cj.continuous
    continuous_invFun := isometry_cj.continuous }

theorem starE_apply (v : CVec3) : starE v = cj v := rfl

/-! ### Derivative operators commute with a real continuous linear equivalence -/

section Equiv

variable {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem dτ_equiv (E : F ≃L[ℝ] G) (Φ : ℝ × Space → F) :
    dτ (fun x => E (Φ x)) = fun x => E (dτ Φ x) := by
  funext p
  have h : (fun x => E (Φ x)) = E ∘ Φ := rfl
  simp only [dτ, h, E.comp_fderiv]
  rfl

theorem dy_equiv (E : F ≃L[ℝ] G) (j : Fin 3) (Φ : ℝ × Space → F) :
    dy j (fun x => E (Φ x)) = fun x => E (dy j Φ x) := by
  funext p
  have h : (fun x => E (Φ x)) = E ∘ Φ := rfl
  simp only [dy, h, E.comp_fderiv]
  rfl

theorem lapT_equiv (E : F ≃L[ℝ] F) (Φ : ℝ × Space → F) :
    lapT (fun x => E (Φ x)) = fun x => E (lapT Φ x) := by
  funext p
  simp only [lapT, dy_equiv, map_sum]

theorem radialT_equiv (E : F ≃L[ℝ] F) (Φ : ℝ × Space → F) :
    radialT (fun x => E (Φ x)) = fun x => E (radialT Φ x) := by
  funext p
  simp only [radialT, dy_equiv, map_sum, map_smul]

theorem driftT_equiv (E : F ≃L[ℝ] F) (Φ : ℝ × Space → F) :
    driftT (fun x => E (Φ x)) = fun x => E (driftT Φ x) := by
  funext p
  simp only [driftT, dτ_equiv, radialT_equiv, map_add, map_neg, map_smul]

theorem isPhaseTest_equiv {P : ℝ} (E : F ≃L[ℝ] G) {Φ : ℝ × Space → F} (h : IsPhaseTest P Φ) :
    IsPhaseTest P (fun x => E (Φ x)) := by
  refine ⟨E.contDiff.comp h.smooth, fun τ y => by simp [h.periodic], ?_⟩
  obtain ⟨R, hR⟩ := h.bounded_support
  exact ⟨R, fun τ y hy => by simp [hR τ y hy]⟩

end Equiv

theorem nuLapT_cj (ν : ℝ) (Φ : ℝ × Space → CVec3) :
    nuLapT ν (fun x => cj (Φ x)) = fun x => cj (nuLapT ν Φ x) := by
  funext p
  have h : lapT (fun x => cj (Φ x)) p = cj (lapT Φ p) := congrFun (lapT_equiv starE Φ) p
  simp only [nuLapT, Pi.smul_apply]
  rw [h, cj_smul_real]

theorem L0T_cj (ν : ℝ) (μ : ℂ) (Φ : ℝ × Space → CVec3) :
    (fun x => L0T ν (fun y => cj (Φ y)) x + μ • cj (Φ x)) =
      fun x => cj (L0T ν Φ x + (starRingEnd ℂ μ) • Φ x) := by
  funext p
  have h1 : driftT (fun x => cj (Φ x)) p = cj (driftT Φ p) := congrFun (driftT_equiv starE Φ) p
  have h2 := congrFun (nuLapT_cj ν Φ) p
  simp only [L0T, Pi.sub_apply, Pi.smul_apply, Pi.add_apply]
  rw [h1, h2]
  simp only [cj_add, cj_sub, cj_smul, cj_smul_real, Complex.conj_conj]


/-! ### The pairing and conjugation -/

theorem dotL_cj (a b : CVec3) : dotL (cj a) b = starRingEnd ℂ (dotL a (cj b)) := by
  simp [dotL_apply, cj_apply, map_sum]

theorem phaseInt_conj (P : ℝ) (g : ℝ × Space → ℂ) :
    phaseInt P (fun x => starRingEnd ℂ (g x)) = starRingEnd ℂ (phaseInt P g) := by
  unfold phaseInt
  rw [Complex.real_smul, Complex.real_smul, map_mul, Complex.conj_ofReal, ← integral_conj]
  congr 2
  funext t
  rw [← integral_conj]

theorem pairF_cj (P : ℝ) (A w : ℝ × Space → CVec3) :
    pairF P (fun x => cj (A x)) w = starRingEnd ℂ (pairF P A (fun x => cj (w x))) := by
  unfold pairF
  rw [← phaseInt_conj]
  congr 1
  funext x
  rw [dotL_cj]

theorem isInYr_cj {P r : ℝ} {f : ℝ × Space → CVec3} (h : IsInYr P r f) :
    IsInYr P r (fun x => cj (f x)) := by
  refine ⟨?_, starE.continuous.comp_aestronglyMeasurable h.meas, ?_⟩
  · filter_upwards [h.periodic] with x hx
    rw [hx]
  · have : phaseLpNorm P r (fun x => cj (f x)) = phaseLpNorm P r f := by
      unfold phaseLpNorm
      have he : ∀ v : CVec3, ‖cj v‖ₑ = ‖v‖ₑ := fun v => by
        rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, norm_cj]
      simp only [he]
    rw [this]; exact h.finite

theorem isSolTest_cj {P : ℝ} {Φ : ℝ × Space → CVec3} (h : IsSolTest P Φ) :
    IsSolTest P (fun x => cj (Φ x)) := by
  refine ⟨isPhaseTest_equiv starE h.1, fun x => ?_⟩
  have e : ∀ j, dy j (fun x => cj (Φ x)) x j = starRingEnd ℂ (dy j Φ x j) := fun j => by
    have : dy j (fun x => cj (Φ x)) x = cj (dy j Φ x) := congrFun (dy_equiv starE j Φ) x
    rw [this]; rfl
  simp only [e]
  rw [← map_sum, h.2 x, map_zero]

theorem gradT_cj (φ : ℝ × Space → ℂ) :
    gradT (fun x => starRingEnd ℂ (φ x)) = fun x => cj (gradT φ x) := by
  funext p
  have e : ∀ j, dy j (fun x => starRingEnd ℂ (φ x)) p = starRingEnd ℂ (dy j φ p) := fun j => by
    have := congrFun (dy_equiv Complex.conjCLE j φ) p
    exact this
  simp only [gradT, e, cj_sum, cj_smul]
  congr 1; funext j
  congr 1; ext i; simp [cj_apply]

theorem hasPtwOp_cj {P : ℝ} {Lt : (ℝ × Space → CVec3) → ℝ × Space → CVec3}
    (hLt : ∀ Φ, Lt (fun x => cj (Φ x)) = fun x => cj (Lt Φ x))
    {w a : ℝ × Space → CVec3} (h : HasPtwOp P Lt w a) :
    HasPtwOp P Lt (fun x => cj (w x)) (fun x => cj (a x)) := by
  intro Φ hΦ
  have := h _ (isPhaseTest_equiv starE hΦ)
  change pairF P (Lt fun x => cj (Φ x)) w = pairF P (fun x => cj (Φ x)) a at this
  rw [hLt, pairF_cj, pairF_cj] at this
  exact (RingHom.injective _) this

theorem isFreeResponse_cj {ν : ℝ} {μ : ℂ} {r P : ℝ} {f w : ℝ × Space → CVec3}
    (h : IsFreeResponse ν μ r P f w) :
    IsFreeResponse ν (starRingEnd ℂ μ) r P (fun x => cj (f x)) (fun x => cj (w x)) := by
  refine ⟨isInYr_cj h.mem_w, ?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, hop⟩ := h.lapl
    exact ⟨fun x => cj (a x), isInYr_cj ha, hasPtwOp_cj (nuLapT_cj ν) hop⟩
  · obtain ⟨a, ha, hop⟩ := h.drift
    exact ⟨fun x => cj (a x), isInYr_cj ha, hasPtwOp_cj (fun Φ => driftT_equiv starE Φ) hop⟩
  · intro φ hφ
    have := h.solenoidal _ (isPhaseTest_equiv Complex.conjCLE hφ)
    have e : gradT (fun x => starRingEnd ℂ (φ x)) = fun x => cj (gradT φ x) := gradT_cj φ
    have hh : gradT (fun x => Complex.conjCLE (φ x)) = fun x => cj (gradT φ x) := gradT_cj φ
    rw [hh, pairF_cj] at this
    exact (map_eq_zero _).1 this
  · intro Φ hΦ
    have := h.equation _ (isSolTest_cj hΦ)
    rw [L0T_cj ν μ Φ, pairF_cj, pairF_cj] at this
    exact (RingHom.injective _) this


/-! ### Conjugation of profiles -/

/-- Conjugation of meridional profile values. -/
def cjM (v : CMerid) : CMerid := WithLp.toLp 2 fun i => starRingEnd ℂ (v i)

theorem norm_cjM (v : CMerid) : ‖cjM v‖ = ‖v‖ := by
  simp [EuclideanSpace.norm_eq, cjM]

theorem cj_realC (u : Space) : cj (UnforcedLeray.B0412.realC u) = UnforcedLeray.B0412.realC u := by
  ext i; simp [cj_apply, UnforcedLeray.B0412.realC_apply]

theorem realC_smul' (k : ℝ) (u : Space) :
    UnforcedLeray.B0412.realC (k • u) = (k : ℂ) • UnforcedLeray.B0412.realC u := by
  ext i; simp [UnforcedLeray.B0412.realC_apply]

theorem nvC_cjM (R : ℝ) (b : CProf) (x : ℝ × Space) :
    NvC R (fun z => cjM (b z)) x = cj (NvC R b x) := by
  have h1 : (fun z => reM (cjM (b z))) = fun z => reM (b z) := by
    funext z; ext i; simp [reM, cjM]
  have h2 : (fun z => imM (cjM (b z))) = (-1 : ℝ) • fun z => imM (b z) := by
    funext z; ext i; simp [imM, cjM]
  unfold NvC
  rw [h1, h2, Axi.Nv_smul, realC_smul', cj_add, cj_realC, cj_smul]
  simp [cj_realC]

theorem inHr_cjM {c r : ℝ} {b : CProf} (h : InHr c r b) : InHr c r (fun z => cjM (b z)) := by
  have hc : Continuous (cjM : CMerid → CMerid) := by
    have : Isometry cjM := Isometry.of_dist_eq fun u v => by
      rw [dist_eq_norm, dist_eq_norm, ← norm_cjM (u - v)]
      congr 1; ext i; simp [cjM]
    exact this.continuous
  refine ⟨?_, hc.comp_aestronglyMeasurable h.meas, ?_⟩
  · filter_upwards [h.periodic] with x hx
    simp only [hx]
  · unfold hNorm
    rw [eLpNorm_congr_norm_ae (g := b) (Eventually.of_forall fun x => norm_cjM (b x))]
    exact h.finite

theorem physRespReal_proof : PhysRespReal := by
  intro ν c ε hν hc hε f b hb hresp
  have hr1 : (1 : ℝ) < bgp := by norm_num [bgp]
  have hF : InHr c bgp (toProf c f) := RespOp.inHr_toProf hc f
  have hbc : InHr c bgp (fun z => cjM (b z)) := inHr_cjM hb
  have hrc : IsResponse ν c ε 0 bgp (toProf c f) (fun z => cjM (b z)) := by
    have h := isFreeResponse_cj hresp
    rw [map_zero] at h
    have hF' : (fun x => cj (NvC ε⁻¹ (toProf c f) x)) = NvC ε⁻¹ (toProf c f) := by
      funext x; rw [RespOp.nvC_toProf_eq_realC, cj_realC]
    have hb' : (fun x => cj (NvC ε⁻¹ b x)) = NvC ε⁻¹ (fun z => cjM (b z)) := by
      funext x; rw [nvC_cjM]
    unfold IsResponse
    rw [← hb']
    rw [hF'] at h
    exact h
  have hs := isResponse_smul (1 / 2 : ℂ) hc hε hr1 (inHr_add hF hF) (inHr_add hb hbc)
    (isResponse_add hc hε hr1 hF hF hb hbc hresp hrc)
  refine ⟨(1 / 2 : ℂ) • (b + fun z => cjM (b z)), inHr_smul _ (inHr_add hb hbc), ?_, ?_⟩
  · intro x i
    simp [cjM]
  · have e : (1 / 2 : ℂ) • (toProf c f + toProf c f) = toProf c f := by
      funext x
      simp only [Pi.smul_apply, Pi.add_apply]
      rw [← two_smul ℂ (toProf c f x), smul_smul]; norm_num
    rw [e] at hs
    exact hs

end RespRealD

theorem physRespReal : PhysRespReal := RespRealD.physRespReal_proof

end UnforcedLeray.Short.IIb
