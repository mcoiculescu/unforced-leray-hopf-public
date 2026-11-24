import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T18
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ResponseProfile
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.ChartDrift.NvCLin
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows
import UnforcedLeray.Short.PartIIb.Tasks.LpBound23over8

/-!
# Linearity of responses, weak derivatives, and observation operators (`PartII-b:T18/1` helper)

Source of record: `the November 2 reference manuscript`, lines 1912-1938, 1992-2004.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.HrOpHelp

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Short.PartIIa

/-! ## `InHr` linearity -/

theorem inHr_add {c r : ℝ} {b b' : CProf} (h : InHr c r b) (h' : InHr c r b') :
    InHr c r (b + b') := by
  refine ⟨?_, h.meas.add h'.meas, ?_⟩
  · filter_upwards [h.periodic, h'.periodic] with x hx hx'
    simp only [Pi.add_apply, hx, hx']
  · have hle := eLpNorm_add_le' h.meas h'.meas (ENNReal.ofReal r)
    exact lt_of_le_of_lt hle
      (ENNReal.mul_lt_top (ENNReal.LpAddConst_lt_top _)
        (ENNReal.add_lt_top.2 ⟨h.finite, h'.finite⟩))

theorem inHr_smul {c r : ℝ} (a : ℂ) {b : CProf} (h : InHr c r b) :
    InHr c r (a • b) := by
  refine ⟨?_, h.meas.const_smul a, ?_⟩
  · filter_upwards [h.periodic] with x hx
    simp only [Pi.smul_apply, hx]
  · unfold hNorm
    rw [eLpNorm_const_smul]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top h.finite

/-! ## `HasWeakVec` linearity -/

theorem hasWeakFO_add {v : Coord → Fin 3 → ℝ} {d : Coord → ℝ} {u u' g g' : Coord → ℂ}
    (h : HasWeakFO v d u g) (h' : HasWeakFO v d u' g') :
    HasWeakFO v d (fun x => u x + u' x) (fun x => g x + g' x) := by
  refine ⟨fun φ hφ => ⟨?_, ?_⟩, fun φ hφ => ?_⟩
  · simp only [add_mul]
    exact (h.1 φ hφ).1.add (h'.1 φ hφ).1
  · simp only [add_mul] at *
    exact (h.1 φ hφ).2.add (h'.1 φ hφ).2
  · dsimp only
    have e : (fun x => (g x + g' x) * (φ x : ℂ))
        = fun x => g x * (φ x : ℂ) + g' x * (φ x : ℂ) := by funext x; ring
    have e' : (fun x => (u x + u' x) * (coordTranspose v d φ x : ℂ))
        = fun x => u x * (coordTranspose v d φ x : ℂ) + u' x * (coordTranspose v d φ x : ℂ) := by
      funext x; ring
    rw [e, e', integral_add (h.1 φ hφ).2 (h'.1 φ hφ).2,
      integral_add (h.1 φ hφ).1 (h'.1 φ hφ).1, h.2 φ hφ, h'.2 φ hφ]

theorem hasWeakVec_add {v : Coord → Fin 3 → ℝ} {d : Coord → ℝ} {b b' g g' : CProf}
    (h : HasWeakVec v d b g) (h' : HasWeakVec v d b' g') :
    HasWeakVec v d (b + b') (g + g') := by
  intro i
  show HasWeakFO v d (fun x => (b + b') x i) (fun x => (g + g') x i)
  simp only [Pi.add_apply, PiLp.add_apply]
  exact hasWeakFO_add (h i) (h' i)

theorem hasWeakFO_smul (a : ℂ) {v : Coord → Fin 3 → ℝ} {d : Coord → ℝ} {u g : Coord → ℂ}
    (h : HasWeakFO v d u g) :
    HasWeakFO v d (fun x => a * u x) (fun x => a * g x) := by
  refine ⟨fun φ hφ => ⟨?_, ?_⟩, fun φ hφ => ?_⟩
  · simp only [mul_assoc]
    exact (h.1 φ hφ).1.const_mul a
  · simp only [mul_assoc] at *
    exact (h.1 φ hφ).2.const_mul a
  · dsimp only
    simp only [mul_assoc, integral_const_mul, h.2 φ hφ]

theorem hasWeakVec_smul (a : ℂ) {v : Coord → Fin 3 → ℝ} {d : Coord → ℝ} {b g : CProf}
    (h : HasWeakVec v d b g) :
    HasWeakVec v d (a • b) (a • g) := by
  intro i
  show HasWeakFO v d (fun x => (a • b) x i) (fun x => (a • g) x i)
  simp only [Pi.smul_apply, PiLp.smul_apply, smul_eq_mul]
  exact hasWeakFO_smul a (h i)

/-! ## `InFlatClass` and `IsFlatResponse` linearity -/

theorem sqrtS_add (b b' : CProf) : sqrtS (b + b') = sqrtS b + sqrtS b' := by
  funext x
  simp only [sqrtS, Pi.add_apply, smul_add]

theorem sqrtS_smul (a : ℂ) (b : CProf) : sqrtS (a • b) = a • sqrtS b := by
  funext x
  ext i
  simp only [sqrtS, Pi.smul_apply, PiLp.smul_apply, smul_eq_mul]
  ring

theorem inFlatClass_add {c r : ℝ} {b b' : CProf}
    (hb : InFlatClass c r b) (hb' : InFlatClass c r b') :
    InFlatClass c r (b + b') := by
  obtain ⟨Sb, Qb, Eb, hS, hQ, hE, hSi, hQi, hEi⟩ := hb.deriv
  obtain ⟨Sb', Qb', Eb', hS', hQ', hE', hSi', hQi', hEi'⟩ := hb'.deriv
  refine ⟨inHr_add hb.inHr hb'.inHr, Sb + Sb', Qb + Qb', Eb + Eb',
    hasWeakVec_add hS hS', hasWeakVec_add hQ hQ', hasWeakVec_add hE hE',
    inHr_add hSi hSi', ?_, ?_⟩
  · rw [sqrtS_add]; exact inHr_add hQi hQi'
  · rw [sqrtS_add]; exact inHr_add hEi hEi'

theorem inFlatClass_smul {c r : ℝ} (a : ℂ) {b : CProf} (hb : InFlatClass c r b) :
    InFlatClass c r (a • b) := by
  obtain ⟨Sb, Qb, Eb, hS, hQ, hE, hSi, hQi, hEi⟩ := hb.deriv
  refine ⟨inHr_smul a hb.inHr, a • Sb, a • Qb, a • Eb,
    hasWeakVec_smul a hS, hasWeakVec_smul a hQ, hasWeakVec_smul a hE,
    inHr_smul a hSi, ?_, ?_⟩
  · rw [sqrtS_smul]; exact inHr_smul a hQi
  · rw [sqrtS_smul]; exact inHr_smul a hEi

theorem isFlatResponse_add {ν : ℝ} {μ : ℂ} {F₁ F₂ b₁ b₂ : CProf}
    (hb₁ : IsFlatResponse ν μ F₁ b₁) (hb₂ : IsFlatResponse ν μ F₂ b₂) :
    IsFlatResponse ν μ (F₁ + F₂) (b₁ + b₂) := by
  refine ⟨fun φ hφ => ?_, fun Ψ hΨ => ?_⟩
  · obtain ⟨i1, e1⟩ := hb₁.solenoidal φ hφ
    obtain ⟨i2, e2⟩ := hb₂.solenoidal φ hφ
    have hfun : (fun x : Coord => (b₁ + b₂) x 0 * (cpd 1 φ x : ℂ) + (b₁ + b₂) x 1 * (cpd 2 φ x : ℂ))
        = fun x => (b₁ x 0 * (cpd 1 φ x : ℂ) + b₁ x 1 * (cpd 2 φ x : ℂ)) +
            (b₂ x 0 * (cpd 1 φ x : ℂ) + b₂ x 1 * (cpd 2 φ x : ℂ)) := by
      funext x; simp only [Pi.add_apply, PiLp.add_apply]; ring
    rw [hfun]
    refine ⟨i1.add i2, ?_⟩
    rw [integral_add i1 i2, e1, e2, add_zero]
  · obtain ⟨i1, j1, e1⟩ := hb₁.equation Ψ hΨ
    obtain ⟨i2, j2, e2⟩ := hb₂.equation Ψ hΨ
    have hsum : (fun x : Coord => ∑ i : Fin 2, (b₁ + b₂) x i * flatTranspose ν μ Ψ x i)
        = fun x => (∑ i : Fin 2, b₁ x i * flatTranspose ν μ Ψ x i) +
            (∑ i : Fin 2, b₂ x i * flatTranspose ν μ Ψ x i) := by
      funext x; simp only [Pi.add_apply, PiLp.add_apply, add_mul, Finset.sum_add_distrib]
    have hcdot : cdot (F₁ + F₂) Ψ = fun x => cdot F₁ Ψ x + cdot F₂ Ψ x := by
      funext x; simp only [cdot, Pi.add_apply, PiLp.add_apply, add_mul, Finset.sum_add_distrib]
    refine ⟨?_, ?_, ?_⟩
    · rw [hsum]; exact i1.add i2
    · rw [hcdot]; exact j1.add j2
    · rw [hsum, hcdot, integral_add i1 i2, integral_add j1 j2, e1, e2]

theorem isFlatResponse_smul {ν : ℝ} {μ : ℂ} (a : ℂ) {F b : CProf}
    (hb : IsFlatResponse ν μ F b) :
    IsFlatResponse ν μ (a • F) (a • b) := by
  refine ⟨fun φ hφ => ?_, fun Ψ hΨ => ?_⟩
  · obtain ⟨i1, e1⟩ := hb.solenoidal φ hφ
    have hfun : (fun x : Coord => (a • b) x 0 * (cpd 1 φ x : ℂ) + (a • b) x 1 * (cpd 2 φ x : ℂ))
        = fun x => a * (b x 0 * (cpd 1 φ x : ℂ) + b x 1 * (cpd 2 φ x : ℂ)) := by
      funext x; simp only [Pi.smul_apply, PiLp.smul_apply, smul_eq_mul]; ring
    rw [hfun]
    refine ⟨i1.const_mul a, ?_⟩
    rw [integral_const_mul, e1, mul_zero]
  · obtain ⟨i1, j1, e1⟩ := hb.equation Ψ hΨ
    have hsum : (fun x : Coord => ∑ i : Fin 2, (a • b) x i * flatTranspose ν μ Ψ x i)
        = fun x => a * ∑ i : Fin 2, b x i * flatTranspose ν μ Ψ x i := by
      funext x
      simp only [Fin.sum_univ_two, Pi.smul_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    have hcdot : cdot (a • F) Ψ = fun x => a * cdot F Ψ x := by
      funext x
      simp only [cdot, Fin.sum_univ_two, Pi.smul_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    refine ⟨?_, ?_, ?_⟩
    · rw [hsum]; exact i1.const_mul a
    · rw [hcdot]; exact j1.const_mul a
    · rw [hsum, hcdot, integral_const_mul, integral_const_mul, e1]

/-! ## `IsResponse` linearity via `HasRepY` and `isFreeResponse_iff` -/

theorem nvC_add (R : ℝ) (b b' : CProf) : NvC R (b + b') = NvC R b + NvC R b' := by
  funext p
  have h := nvCLin_proof R 1 b (-b') p
  have heq : (fun x => (1 : ℂ) • b x - (-b') x) = b + b' := by
    funext x; simp [Pi.add_apply]
  have hneg : NvC R (-b') p = -NvC R b' p := by
    have h0 := nvCLin_proof R 0 b b' p
    have heq1 : (fun x => (0 : ℂ) • b x - b' x) = -b' := by funext x; simp
    rw [heq1, zero_smul, zero_sub] at h0
    exact h0
  rw [heq, one_smul, hneg, sub_neg_eq_add] at h
  exact h

theorem nvC_smul (R : ℝ) (a : ℂ) (b : CProf) : NvC R (a • b) = a • NvC R b := by
  funext p
  have h := nvCLin_proof R a b 0 p
  have h0 := nvCLin_proof R 0 b 0 p
  have heq0 : (fun x => (0 : ℂ) • b x - (0 : CProf) x) = 0 := by funext x; simp
  rw [heq0, zero_smul, zero_sub] at h0
  have hNv0 : NvC R 0 p = 0 := by
    have : (2 : ℂ) • NvC R 0 p = 0 := by
      rw [two_smul]
      nth_rw 2 [h0]
      exact add_neg_cancel _
    exact (smul_eq_zero.1 this).resolve_left (by norm_num)
  have heqa : (fun x => a • b x - (0 : CProf) x) = a • b := by funext x; simp
  rw [heqa, hNv0, sub_zero] at h
  exact h

theorem hasRepY_add_eq {P : ℝ} [Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)]
    {F₁ F₂ F₁₂ : Yq P q} {f₁ f₂ : ℝ × Space → CVec3}
    (h₁ : HasRepY F₁ f₁) (h₂ : HasRepY F₂ f₂) (h₁₂ : HasRepY F₁₂ (f₁ + f₂)) :
    F₁₂ = F₁ + F₂ := by
  apply eq_of_forall_phasePair
  intro Φ hΦ
  rw [phasePair_eq_periodIntegral hΦ F₁₂, phasePair_eq_periodIntegral hΦ (F₁ + F₂)]
  congr 1
  have hP0 : (0 : ℝ) < P := Fact.out
  have hτ : ∀ᵐ τ ∂(volume : Measure (AddCircle P)), (F₁ + F₂) τ = F₁ τ + F₂ τ := by
    rw [AddCircle.volume_eq_smul_haarAddCircle,
      Measure.ae_ennreal_smul_measure_eq (ENNReal.ofReal_pos.2 hP0).ne']
    exact Lp.coeFn_add F₁ F₂
  have hae := (AddCircle.measurePreserving_mk (T := P) 0).quasiMeasurePreserving.ae
    (p := fun τ : AddCircle P => (F₁ + F₂) τ = F₁ τ + F₂ τ) hτ
  apply integral_congr_ae
  filter_upwards [hae, ae_restrict_of_ae h₁.slice, ae_restrict_of_ae h₂.slice,
    ae_restrict_of_ae h₁₂.slice] with t ht hs₁ hs₂ hs₁₂
  refine integral_congr_ae ?_
  filter_upwards [hs₁, hs₂, hs₁₂,
    Lp.coeFn_add (F₁ (t : AddCircle P)) (F₂ (t : AddCircle P))] with y hy₁ hy₂ hy₁₂ hadd
  rw [ht, hadd, Pi.add_apply, ← hy₁, ← hy₂, ← hy₁₂]
  rfl

theorem hasRepY_smul_eq {P : ℝ} [Fact (0 < P)] {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (a : ℂ) {F Fa : Yq P q} {f : ℝ × Space → CVec3}
    (h : HasRepY F f) (ha : HasRepY Fa (a • f)) :
    Fa = a • F := by
  apply eq_of_forall_phasePair
  intro Φ hΦ
  rw [phasePair_eq_periodIntegral hΦ Fa, phasePair_eq_periodIntegral hΦ (a • F)]
  congr 1
  have hP0 : (0 : ℝ) < P := Fact.out
  have hτ : ∀ᵐ τ ∂(volume : Measure (AddCircle P)), (a • F) τ = a • F τ := by
    rw [AddCircle.volume_eq_smul_haarAddCircle,
      Measure.ae_ennreal_smul_measure_eq (ENNReal.ofReal_pos.2 hP0).ne']
    exact Lp.coeFn_smul a F
  have hae := (AddCircle.measurePreserving_mk (T := P) 0).quasiMeasurePreserving.ae
    (p := fun τ : AddCircle P => (a • F) τ = a • F τ) hτ
  apply integral_congr_ae
  filter_upwards [hae, ae_restrict_of_ae h.slice, ae_restrict_of_ae ha.slice]
    with t ht hs hsa
  refine integral_congr_ae ?_
  filter_upwards [hs, hsa, Lp.coeFn_smul a (F (t : AddCircle P))] with y hy hya hsmul
  rw [ht, hsmul, Pi.smul_apply, ← hy, ← hya]
  rfl

theorem isResponse_add {c ε ν r : ℝ} {μ : ℂ} {F₁ F₂ b₁ b₂ : CProf}
    (hc : 0 < c) (hε : 0 < ε) (hr1 : 1 < r)
    (hF₁ : InHr c r F₁) (hF₂ : InHr c r F₂)
    (hb₁ : InHr c r b₁) (hb₂ : InHr c r b₂)
    (hresp₁ : IsResponse ν c ε μ r F₁ b₁) (hresp₂ : IsResponse ν c ε μ r F₂ b₂) :
    IsResponse ν c ε μ r (F₁ + F₂) (b₁ + b₂) := by
  set P := 2 * ε * c
  have hP : 0 < P := by positivity
  have : Fact (0 < P) := ⟨hP⟩
  have hr0 : 0 < r := by linarith
  set q := ENNReal.ofReal r
  have h1' : 1 < q := ENNReal.one_lt_ofReal.2 hr1
  have : Fact (1 ≤ q) := ⟨h1'.le⟩
  have hf₁ : IsInYr P r (NvC ε⁻¹ F₁) := nvCInYr_proof c ε r F₁ hc hε hr0 hF₁
  have hf₂ : IsInYr P r (NvC ε⁻¹ F₂) := nvCInYr_proof c ε r F₂ hc hε hr0 hF₂
  have hf₁₂ : IsInYr P r (NvC ε⁻¹ (F₁ + F₂)) :=
    nvCInYr_proof c ε r (F₁ + F₂) hc hε hr0 (inHr_add hF₁ hF₂)
  have hw₁ : IsInYr P r (NvC ε⁻¹ b₁) := nvCInYr_proof c ε r b₁ hc hε hr0 hb₁
  have hw₂ : IsInYr P r (NvC ε⁻¹ b₂) := nvCInYr_proof c ε r b₂ hc hε hr0 hb₂
  have hw₁₂ : IsInYr P r (NvC ε⁻¹ (b₁ + b₂)) :=
    nvCInYr_proof c ε r (b₁ + b₂) hc hε hr0 (inHr_add hb₁ hb₂)
  obtain ⟨Ff₁, hFf₁, -⟩ := exists_hasRepY P r hr0 _ hf₁
  obtain ⟨Ff₂, hFf₂, -⟩ := exists_hasRepY P r hr0 _ hf₂
  obtain ⟨Ff₁₂, hFf₁₂, -⟩ := exists_hasRepY P r hr0 _ hf₁₂
  obtain ⟨W₁, hW₁, -⟩ := exists_hasRepY P r hr0 _ hw₁
  obtain ⟨W₂, hW₂, -⟩ := exists_hasRepY P r hr0 _ hw₂
  obtain ⟨W₁₂, hW₁₂, -⟩ := exists_hasRepY P r hr0 _ hw₁₂
  have hFf_eq : Ff₁₂ = Ff₁ + Ff₂ := by
    rw [nvC_add] at hFf₁₂
    exact hasRepY_add_eq hFf₁ hFf₂ hFf₁₂
  have hW_eq : W₁₂ = W₁ + W₂ := by
    rw [nvC_add] at hW₁₂
    exact hasRepY_add_eq hW₁ hW₂ hW₁₂
  obtain ⟨-, D₁, hs₁, hb₁'⟩ :=
    (isFreeResponse_iff hr0 lerayPairSol solSeparation hr1 hFf₁ hW₁).1 hresp₁
  obtain ⟨-, D₂, hs₂, hb₂'⟩ :=
    (isFreeResponse_iff hr0 lerayPairSol solSeparation hr1 hFf₂ hW₂).1 hresp₂
  refine (isFreeResponse_iff hr0 lerayPairSol solSeparation hr1 hFf₁₂ hW₁₂).2 ⟨hw₁₂, ?_⟩
  subst hFf_eq hW_eq
  refine ⟨Submodule.add_mem _ D₁ D₂, Submodule.add_mem _ hs₁ hs₂, ?_⟩
  have hsub : (⟨W₁ + W₂, Submodule.add_mem _ D₁ D₂⟩ : D P ν q) = ⟨W₁, D₁⟩ + ⟨W₂, D₂⟩ := rfl
  rw [hsub, map_add, map_add, hb₁', hb₂']

theorem isResponse_smul {c ε ν r : ℝ} {μ : ℂ} (a : ℂ) {F b : CProf}
    (hc : 0 < c) (hε : 0 < ε) (hr1 : 1 < r)
    (hF : InHr c r F) (hb : InHr c r b) (hresp : IsResponse ν c ε μ r F b) :
    IsResponse ν c ε μ r (a • F) (a • b) := by
  set P := 2 * ε * c
  have hP : 0 < P := by positivity
  have : Fact (0 < P) := ⟨hP⟩
  have hr0 : 0 < r := by linarith
  set q := ENNReal.ofReal r
  have h1' : 1 < q := ENNReal.one_lt_ofReal.2 hr1
  have : Fact (1 ≤ q) := ⟨h1'.le⟩
  have hf : IsInYr P r (NvC ε⁻¹ F) := nvCInYr_proof c ε r F hc hε hr0 hF
  have hfa : IsInYr P r (NvC ε⁻¹ (a • F)) :=
    nvCInYr_proof c ε r (a • F) hc hε hr0 (inHr_smul a hF)
  have hw : IsInYr P r (NvC ε⁻¹ b) := nvCInYr_proof c ε r b hc hε hr0 hb
  have hwa : IsInYr P r (NvC ε⁻¹ (a • b)) :=
    nvCInYr_proof c ε r (a • b) hc hε hr0 (inHr_smul a hb)
  obtain ⟨Ff, hFf, -⟩ := exists_hasRepY P r hr0 _ hf
  obtain ⟨Ffa, hFfa, -⟩ := exists_hasRepY P r hr0 _ hfa
  obtain ⟨W, hW, -⟩ := exists_hasRepY P r hr0 _ hw
  obtain ⟨Wa, hWa, -⟩ := exists_hasRepY P r hr0 _ hwa
  have hFf_eq : Ffa = a • Ff := by
    rw [nvC_smul] at hFfa
    exact hasRepY_smul_eq a hFf hFfa
  have hW_eq : Wa = a • W := by
    rw [nvC_smul] at hWa
    exact hasRepY_smul_eq a hW hWa
  obtain ⟨-, D₁, hs₁, hb₁'⟩ :=
    (isFreeResponse_iff hr0 lerayPairSol solSeparation hr1 hFf hW).1 hresp
  refine (isFreeResponse_iff hr0 lerayPairSol solSeparation hr1 hFfa hWa).2 ⟨hwa, ?_⟩
  subst hFf_eq hW_eq
  refine ⟨Submodule.smul_mem _ a D₁, Submodule.smul_mem _ a hs₁, ?_⟩
  have hsub : (⟨a • W, Submodule.smul_mem _ a D₁⟩ : D P ν q) = a • ⟨W, D₁⟩ := rfl
  rw [hsub, map_smul, map_smul, hb₁']

/-! ## Pointwise linearity of `dqOf` and `ObsOp.apply` -/

theorem dqOf_add (ε : ℝ) (b₁ Sb₁ Qb₁ Eb₁ b₂ Sb₂ Qb₂ Eb₂ : CProf) :
    dqOf ε (b₁ + b₂) (Sb₁ + Sb₂) (Qb₁ + Qb₂) (Eb₁ + Eb₂) =
      dqOf ε b₁ Sb₁ Qb₁ Eb₁ + dqOf ε b₂ Sb₂ Qb₂ Eb₂ := by
  funext x
  ext i
  simp only [dqOf, Pi.add_apply, PiLp.add_apply]
  ring

theorem dqOf_smul (ε : ℝ) (a : ℂ) (b Sb Qb Eb : CProf) :
    dqOf ε (a • b) (a • Sb) (a • Qb) (a • Eb) = a • dqOf ε b Sb Qb Eb := by
  funext x
  ext i
  simp only [dqOf, Pi.smul_apply, PiLp.smul_apply, smul_eq_mul]
  ring

theorem obsOp_apply_add {σ H₁ L₁ Γ : ℝ} (B : ObsOp σ H₁ L₁ Γ)
    (d₁ gq₁ gη₁ d₂ gq₂ gη₂ : CProf) :
    B.apply (d₁ + d₂) (gq₁ + gq₂) (gη₁ + gη₂) =
      B.apply d₁ gq₁ gη₁ + B.apply d₂ gq₂ gη₂ := by
  funext x
  simp only [ObsOp.apply, Pi.add_apply, map_add]
  abel

theorem obsOp_apply_smul {σ H₁ L₁ Γ : ℝ} (B : ObsOp σ H₁ L₁ Γ)
    (a : ℂ) (d gq gη : CProf) :
    B.apply (a • d) (a • gq) (a • gη) = a • B.apply d gq gη := by
  funext x
  simp only [ObsOp.apply, Pi.smul_apply, map_smul, smul_add]

end UnforcedLeray.Short.IIb.HrOpHelp

end
