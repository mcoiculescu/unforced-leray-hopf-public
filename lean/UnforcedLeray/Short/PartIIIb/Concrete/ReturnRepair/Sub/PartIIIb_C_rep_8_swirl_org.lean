import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1_org

/-!
# `PartIII-b:C/rep/8/swirl/org`: the swirl-free hypothesis on the error families

Source of record: `the November 2 reference manuscript` (73 pages), lines 5376
(`T = (T₁,T₂) = M_U w`), 5141-5142 (`w`, `U` swirl free), 4772-4774 (`Σ_M` has the zero azimuthal
row and column), 5484-5531, 5607-5627, 5640-5662 (`𝓔_ν = {T = M w}`), 5687-5697.

Step (a) (`MeanComparisonAzi`, `PartIII-b_C_rep_8_1_org`) holds only for swirl-free thin stresses
(`ThinAziZero`).  `ThinCompleteAt` and `ThinBodyMarginAt` (`Estimates.lean`) quantify over all
`T : LStr` and are false for a thin stress with a hoop entry; here their bodies are restated under
`ThinAziZero T` (`ThinCompleteAziAt`, `ThinBodyMarginAziAt`), with
* `thinCompleteAzi_of`: the three-way split of `rep_8_org` with `MeanComparisonAzi`
  (`RingExpansion`, `GaussianReplace` stay for all `T`);
* `errorFamilyBoundsAzi_of`: `errorFamilyBounds_of` with `ThinBodyMarginAzi`, the swirl-free
  hypothesis being discharged on the pair space `T = M w` by `hM`, i.e. by the lemma
  `ThinAziZero Pl K L (multOp Pl K L w)` (organizer follow-up task `multOp_thinAziZero`: `multOp`
  is the transport of `nearMU`, whose `IsSplitMult` first output is `symOuter (chartCoeff R V p)
  (u p)` with vanishing azimuthal row and column).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

section Defs

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)

/-- `ThinCompleteAt` (`repair:thin-complete`, source 5484-5506) for swirl-free thin stresses
(`ThinAziZero`, source 5376, 5141-5142, 4772-4774). -/
def ThinCompleteAziAt (C : ℝ) (k : ℕ) (Csig bsig : ℝ) : Prop :=
  ∀ T : LStr Pl K L, ThinAziZero Pl K L T →
    ENNReal.ofReal ‖(wardOps Pl K L μ).2.2 (thinPart T) - EAOp K L μ (LjOp Pl K L μ T)‖ ≤
      ENNReal.ofReal (C * L.ν⁻¹ ^ k * (L.ε ^ 4 + L.ε ^ (85 / 22 : ℝ) * Real.exp (K.m0 / L.ν) +
        L.ε ^ 3 * deltaBase Csig bsig L.ν)) * oldN1 Pl K L T

/-- `ThinBodyMarginAt` (gain band, source 5527-5531) for swirl-free thin stresses. -/
def ThinBodyMarginAziAt (C : ℝ) (k : ℕ) : Prop :=
  ∀ T : LStr Pl K L, ThinAziZero Pl K L T →
    ‖(wardOps Pl K L μ).2.2 (thinPart T) - EAOp K L μ (LjOp Pl K L μ T)‖ ≤
      C * L.ν⁻¹ ^ k * Real.exp (-(gRate Pl / 15 - 3 * K.m0 / 2) / L.ν) * ‖T‖

end Defs

namespace SeqData

variable (D : SeqData)

/-- `ThinCompleteAziAt` along the sequence. -/
def ThinCompleteAzi : Prop :=
  ∃ (C : ℝ) (k : ℕ) (Csig bsig : ℝ), 0 < bsig ∧ ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    ThinCompleteAziAt D.Pl D.K (D.level n) (D.mu n z) C k Csig bsig

/-- `ThinBodyMarginAziAt` along the sequence. -/
def ThinBodyMarginAzi : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
    ThinBodyMarginAziAt D.Pl D.K (D.level n) (D.mu n z) C k

end SeqData

/-! ## 1. The assembly of `ThinCompleteAzi` -/

section Assembly

variable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)

/-- **`thinCompleteAt_of`**: the three bounds give `ThinCompleteAt` at one regime. -/
theorem thinCompleteAziAt_of (hpin : RegimePins Pl K L μ) {C : ℝ} (hC : 0 ≤ C) {k : ℕ}
    {Csig bsig : ℝ} (h1 : MeanComparisonAziAt Pl K L μ C k) (h2 : RingExpansionAt Pl K L μ C k)
    (h3 : GaussianReplaceAt Pl K L μ C k Csig bsig) :
    ThinCompleteAziAt Pl K L μ (3 * C) k Csig bsig := by
  intro T hT
  set μs := srcMeasure (cOf L.ν) with hμs
  set W := (wardOps Pl K L μ).2.2 (thinPart T) with hW
  set E := EAOp K L μ (LjOp Pl K L μ T) with hE
  set A := LjFun (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν L.ε μ K.χo K.χy T with hA
  have hward := Classical.epsilon_spec hpin.ward
  have hWae : (W : Chart → Merid) =ᵐ[μs] actualE Pl K L μ T :=
    (hward (thinPart T) _ _ Filter.EventuallyEq.rfl Filter.EventuallyEq.rfl).2.2
  have hLj : affIota K.as (LjOp Pl K L μ T) = A := Classical.epsilon_spec hpin.lj T
  have hEae : (E : Chart → Merid) =ᵐ[μs] EAcoef L.ν μ K.χf A := by
    have := EAOp_spec hpin.eA (LjOp Pl K L μ T)
    rwa [hLj] at this
  obtain ⟨hm1, b1⟩ := h1 T hT
  obtain ⟨hr3, b3⟩ := h3 T
  have b2 := h2 T
  have hfm : AEStronglyMeasurable (actualE Pl K L μ T) μs :=
    (Lp.aestronglyMeasurable W).congr hWae
  have hem : AEStronglyMeasurable (EAcoef L.ν μ K.χf A) μs :=
    (Lp.aestronglyMeasurable E).congr hEae
  -- norm as eLpNorm
  have hnorm : ENNReal.ofReal ‖W - E‖ =
      eLpNorm (actualE Pl K L μ T - EAcoef L.ν μ K.χf A) 2 μs := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
    refine eLpNorm_congr_ae ?_
    filter_upwards [Lp.coeFn_sub W E, hWae, hEae] with p h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
    rfl
  rw [hnorm]
  have hsplit : actualE Pl K L μ T - EAcoef L.ν μ K.χf A =
      (actualE Pl K L μ T - meanE Pl K L μ T) +
        ((meanE Pl K L μ T - ringAff Pl K L μ T) +
          (ringAff Pl K L μ T - EAcoef L.ν μ K.χf A)) := by
    funext p; simp only [Pi.add_apply, Pi.sub_apply]; abel
  have t1 : eLpNorm (actualE Pl K L μ T - EAcoef L.ν μ K.χf A) 2 μs ≤
      eLpNorm (actualE Pl K L μ T - meanE Pl K L μ T) 2 μs +
        (eLpNorm (meanE Pl K L μ T - ringAff Pl K L μ T) 2 μs +
          eLpNorm (ringAff Pl K L μ T - EAcoef L.ν μ K.χf A) 2 μs) := by
    rw [hsplit]
    refine (eLpNorm_add_le (hfm.sub hm1) ((hm1.sub hr3).add (hr3.sub hem)) (by norm_num)).trans ?_
    gcongr
    exact eLpNorm_add_le (hm1.sub hr3) (hr3.sub hem) (by norm_num)
  have hν := L.ν_pos
  have hε := L.ε_pos
  have hP : 0 ≤ L.ν⁻¹ ^ k := by positivity
  have hδ : 0 ≤ deltaBase Csig bsig L.ν := (Real.exp_pos _).le
  have hX : 0 ≤ L.ε ^ 3 * deltaBase Csig bsig L.ν + L.ε ^ (85 / 22 : ℝ) * Real.exp (K.m0 / L.ν) := by
    positivity
  set N := oldN1 Pl K L T
  set a2 := C * L.ν⁻¹ ^ k *
    (L.ε ^ 4 + L.ε ^ (85 / 22 : ℝ) * Real.exp (K.m0 / L.ν)) with ha2
  set b := C * L.ν⁻¹ ^ k *
    (L.ε ^ 3 * deltaBase Csig bsig L.ν + L.ε ^ (85 / 22 : ℝ) * Real.exp (K.m0 / L.ν)) with hb
  have ha20 : 0 ≤ a2 := by positivity
  have hb0 : 0 ≤ b := by positivity
  have hz : 0 ≤ C * L.ν⁻¹ ^ k * (L.ε ^ 3 * deltaBase Csig bsig L.ν) := by positivity
  have hz2 : 0 ≤ C * L.ν⁻¹ ^ k * (L.ε ^ 4 + L.ε ^ (85 / 22 : ℝ) * Real.exp (K.m0 / L.ν)) := ha20
  calc eLpNorm (actualE Pl K L μ T - EAcoef L.ν μ K.χf A) 2 μs
      ≤ ENNReal.ofReal a2 * N + (ENNReal.ofReal a2 * N + ENNReal.ofReal b * N) :=
        t1.trans (add_le_add b1 (add_le_add b2 b3))
    _ = ENNReal.ofReal (a2 + (a2 + b)) * N := by
        rw [ENNReal.ofReal_add ha20 (add_nonneg ha20 hb0), ENNReal.ofReal_add ha20 hb0]
        ring
    _ ≤ ENNReal.ofReal (3 * C * L.ν⁻¹ ^ k * (L.ε ^ 4 + L.ε ^ (85 / 22 : ℝ) *
          Real.exp (K.m0 / L.ν) + L.ε ^ 3 * deltaBase Csig bsig L.ν)) * N := by
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
        rw [ha2, hb]
        have hx : 0 ≤ C * L.ν⁻¹ ^ k * L.ε ^ 4 := by positivity
        nlinarith [hz, hx]

end Assembly

/-- **`thinComplete`** (swirl-free form; source 5484-5506): the three sequence bounds give
`ThinCompleteAzi`. -/
theorem thinCompleteAzi_of (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp)
    (h1 : D.MeanComparisonAzi) (h2 : D.RingExpansion) (h3 : D.GaussianReplace) :
    D.ThinCompleteAzi := by
  obtain ⟨C1, k1, e1⟩ := h1
  obtain ⟨C2, k2, e2⟩ := h2
  obtain ⟨C3, k3, Csig, bsig, hb, e3⟩ := h3
  have hle := retNu_retEps_eventually_le_one hst.omega_ne hst.gamma_pos D.coeff_ne
  set C : ℝ := |C1| + |C2| + |C3| with hCdef
  set k : ℕ := max k1 (max k2 k3) with hk
  have hC0 : 0 ≤ C := by positivity
  refine ⟨3 * C, k, Csig, bsig, hb, ?_⟩
  filter_upwards [e1, e2, e3, hle, hst.pins] with n a1 a2 a3 hν hp z hz
  have hνp := (D.level n).ν_pos
  have hν1 : (D.level n).ν ≤ 1 := hν.1
  have hε := (D.level n).ε_pos
  have hC1 : C1 ≤ C := (le_abs_self C1).trans (by rw [hCdef]; linarith [abs_nonneg C2, abs_nonneg C3])
  have hC2 : C2 ≤ C := (le_abs_self C2).trans (by rw [hCdef]; linarith [abs_nonneg C1, abs_nonneg C3])
  have hC3 : C3 ≤ C := (le_abs_self C3).trans (by rw [hCdef]; linarith [abs_nonneg C2, abs_nonneg C1])
  refine thinCompleteAziAt_of D.Pl D.K (D.level n) (D.mu n z) (hp z hz) hC0 ?_ ?_ ?_
  · intro T hT
    obtain ⟨m, b⟩ := a1 z hz T hT
    exact ⟨m, bound_mono hνp hν1 (by positivity) hC1 hC0 (le_max_left _ _) b⟩
  · intro T
    exact bound_mono hνp hν1 (by positivity) hC2 hC0
      ((le_max_left k2 k3).trans (le_max_right _ _)) (a2 z hz T)
  · intro T
    obtain ⟨m, b⟩ := a3 z hz T
    refine ⟨m, bound_mono hνp hν1 (by unfold deltaBase; positivity) hC3 hC0
      ((le_max_right k2 k3).trans (le_max_right _ _)) b⟩

/-! ## 2. The error families from the swirl-free estimates -/

set_option maxHeartbeats 1600000 in
/-- **The error families of the concrete sequence** (source 5607-5627, 5687-5697):
`ErrorFamilyBounds (concreteReturnSeq D G) γ ω_b m₀` from the age errors and far velocities, the
gain-band forms of `repair:body-error`, `repair:thin-complete` and
`repair:actual-affine-remainder`, the body inverse on the generated range, and the invertibility of
the near layer (`NearAt`) for large `n`. -/
theorem errorFamilyBoundsAzi_of (D : SeqData)
    (G : ∀ n, AffSp D.K.as →L[ℝ] GrdG (cOf (retNu D.Pl D.σ₀ n))) {ωb : ℝ}
    (hγ : 0 ≤ gRate D.Pl) (hωb : 0 ≤ ωb) (hm0 : 0 ≤ D.K.m0) (hω : D.Pl.eigenvalue.im ≠ 0)
    (hnear : ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, NearAt D.Pl D.K (D.level n) (D.mu n z))
    (h4 : D.AgeError ωb) (h4v : D.AgeVelocity ωb) (h5 : D.BodyRepairMargin)
    (h6 : D.ThinBodyMarginAzi) (h7 : D.AffRemMargin) (hB : D.NearBody)
    (hM : ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1, ∀ w : LVel D.Pl (D.level n),
      ThinAziZero D.Pl D.K (D.level n) (multOp D.Pl D.K (D.level n) w)) :
    ErrorFamilyBounds (concreteReturnSeq D G) (gRate D.Pl) ωb D.K.m0 := by
  obtain ⟨C4, k4, e4⟩ := h4
  obtain ⟨C4v, k4v, e4v⟩ := h4v
  obtain ⟨C5, k5, e5⟩ := h5
  obtain ⟨C6, k6, e6⟩ := h6
  obtain ⟨C7, k7, e7⟩ := h7
  obtain ⟨CB, kB, eB⟩ := hB
  have hν1 : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n ≤ 1 :=
    ((retNu_tendsto D.σ₀ hω).eventually_lt_const one_pos).mono fun n h => h.le
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (hnear.and (hM.and (e4.and (e4v.and (e5.and (e6.and (e7.and (eB.and hν1))))))))
  refine ⟨|C4| + |C4v| + (|CB| * |C5| + |CB| * |C6| + |CB| * |C7|),
    k4 + k4v + kB + k5 + k6 + k7, N, fun n hn z hz V => ?_⟩
  obtain ⟨hnr, hMn, f4, f4v, f5, f6, f7, fB, hν1n⟩ := hN n hn
  have hnz := hnr z hz
  obtain ⟨f4a, f4b⟩ := f4 z hz
  obtain ⟨f4va, f4vb⟩ := f4v z hz
  have f5z := f5 z hz
  have f6z := f6 z hz
  have f7z := f7 z hz
  have fBz := fB z hz
  have hν : 0 < (D.level n).ν := (D.level n).ν_pos
  have hν1' : (D.level n).ν ≤ 1 := hν1n
  have hops := concreteReturnSeq_ops_eq D G n z hnz
  have hMv : ∀ T',
      ((concreteReturnSeq D G).ops n z).M (((concreteReturnSeq D G).ops n z).vQ T') =
      multOp D.Pl D.K (D.level n) (ageVel D.Pl D.K (D.level n) (D.mu n z) T' +
        Rop D.Pl (D.level n) (D.mu n z) ((wardOps D.Pl D.K (D.level n) (D.mu n z)).2.2 T' -
          EAOp D.K (D.level n) (D.mu n z) (LjOp D.Pl D.K (D.level n) (D.mu n z) T') -
          rAOp D.Pl D.K (D.level n) (D.mu n z) (LjOp D.Pl D.K (D.level n) (D.mu n z) T'))) := by
    intro T'; rw [hops]; rfl
  have hvQeq : ∀ T', ((concreteReturnSeq D G).ops n z).vQ T' =
      ageVel D.Pl D.K (D.level n) (D.mu n z) T' +
        Rop D.Pl (D.level n) (D.mu n z) ((wardOps D.Pl D.K (D.level n) (D.mu n z)).2.2 T' -
          EAOp D.K (D.level n) (D.mu n z) (LjOp D.Pl D.K (D.level n) (D.mu n z) T') -
          rAOp D.Pl D.K (D.level n) (D.mu n z) (LjOp D.Pl D.K (D.level n) (D.mu n z) T')) := by
    intro T'; rw [hops]; exact concreteOps_vQ _ _ _ _ hnz T'
  have hgraph : ((concreteReturnSeq D G).ops n z).Tc V =
      multOp D.Pl D.K (D.level n) (((concreteReturnSeq D G).ops n z).wc V) := by
    rw [hops]; exact PairSp.graph V
  rw [hMv, hvQeq]
  generalize (((concreteReturnSeq D G).ops n z).Tc V : LStr D.Pl D.K (D.level n)) = T at hgraph ⊢
  generalize (((concreteReturnSeq D G).ops n z).wc V : LVel D.Pl (D.level n)) = w at hgraph ⊢
  have hTw : T = multOp D.Pl D.K (D.level n) w := hgraph
  -- the five pieces of `v_Q(T)` (source 5687-5697)
  have hsplitT := thinPart_add_repPart T
  have hage : ageVel D.Pl D.K (D.level n) (D.mu n z) (thinPart T) +
      ageVel D.Pl D.K (D.level n) (D.mu n z) (repPart T) =
      ageVel D.Pl D.K (D.level n) (D.mu n z) T := by
    rw [← map_add, hsplitT]
  have hE : (wardOps D.Pl D.K (D.level n) (D.mu n z)).2.2 (thinPart T) +
      (wardOps D.Pl D.K (D.level n) (D.mu n z)).2.2 (repPart T) =
      (wardOps D.Pl D.K (D.level n) (D.mu n z)).2.2 T := by
    rw [← map_add, hsplitT]
  obtain ⟨a1, ha1⟩ : ∃ a, a = ageVel D.Pl D.K (D.level n) (D.mu n z) (thinPart T) := ⟨_, rfl⟩
  obtain ⟨a2, ha2⟩ : ∃ a, a = ageVel D.Pl D.K (D.level n) (D.mu n z) (repPart T) := ⟨_, rfl⟩
  obtain ⟨b1, hb1d⟩ : ∃ b, b = (wardOps D.Pl D.K (D.level n) (D.mu n z)).2.2 (thinPart T) -
      EAOp D.K (D.level n) (D.mu n z) (LjOp D.Pl D.K (D.level n) (D.mu n z) T) := ⟨_, rfl⟩
  obtain ⟨b2, hb2d⟩ : ∃ b, b = (wardOps D.Pl D.K (D.level n) (D.mu n z)).2.2 (repPart T) :=
    ⟨_, rfl⟩
  obtain ⟨b3, hb3d⟩ : ∃ b, b = rAOp D.Pl D.K (D.level n) (D.mu n z)
      (LjOp D.Pl D.K (D.level n) (D.mu n z) T) := ⟨_, rfl⟩
  have hvQ : ageVel D.Pl D.K (D.level n) (D.mu n z) T +
        Rop D.Pl (D.level n) (D.mu n z) ((wardOps D.Pl D.K (D.level n) (D.mu n z)).2.2 T -
          EAOp D.K (D.level n) (D.mu n z) (LjOp D.Pl D.K (D.level n) (D.mu n z) T) -
          rAOp D.Pl D.K (D.level n) (D.mu n z) (LjOp D.Pl D.K (D.level n) (D.mu n z) T)) =
      a1 + a2 + Rop D.Pl (D.level n) (D.mu n z) (b1 + b2 - b3) := by
    rw [← hage, ← hE, ha1, ha2, hb1d, hb2d, hb3d]
    simp only [map_add, map_sub]
    abel
  -- exponential factors
  obtain ⟨eA, heA⟩ : ∃ e, Real.exp (-(gRate D.Pl / 15 - ωb - 3 * D.K.m0 / 2) / (D.level n).ν) = e :=
    ⟨_, rfl⟩
  obtain ⟨eG, heG⟩ : ∃ e,
      Real.exp (-(19 * gRate D.Pl / 66 - ωb - 3 * D.K.m0 / 2) / (D.level n).ν) = e := ⟨_, rfl⟩
  obtain ⟨eχA, heχA⟩ : ∃ e,
      Real.exp ((gRate D.Pl / 10 + ωb + 3 * D.K.m0 / 2) / (D.level n).ν) = e := ⟨_, rfl⟩
  obtain ⟨eχG, heχG⟩ : ∃ e,
      Real.exp (-(31 * gRate D.Pl / 165 - ωb - 3 * D.K.m0 / 2) / (D.level n).ν) = e := ⟨_, rfl⟩
  obtain ⟨eA', heA'⟩ : ∃ e, Real.exp (-(gRate D.Pl / 15 - 3 * D.K.m0 / 2) / (D.level n).ν) = e :=
    ⟨_, rfl⟩
  obtain ⟨eG', heG'⟩ : ∃ e,
      Real.exp (-(19 * gRate D.Pl / 66 - 3 * D.K.m0 / 2) / (D.level n).ν) = e := ⟨_, rfl⟩
  have hdiv : ∀ {a b : ℝ}, a ≤ b → Real.exp (a / (D.level n).ν) ≤ Real.exp (b / (D.level n).ν) :=
    fun h => Real.exp_le_exp.2 (div_le_div_of_nonneg_right h hν.le)
  have hA'A : eA' ≤ eA := by rw [← heA', ← heA]; exact hdiv (by linarith)
  have hG'G : eG' ≤ eG := by rw [← heG', ← heG]; exact hdiv (by linarith)
  have hA'χ : eA' ≤ eχA := by rw [← heA', ← heχA]; exact hdiv (by linarith)
  have hG'χ : eG' ≤ eχG := by rw [← heG', ← heχG]; exact hdiv (by linarith)
  have hA'0 : 0 ≤ eA' := by rw [← heA']; exact (Real.exp_pos _).le
  have hG'0 : 0 ≤ eG' := by rw [← heG']; exact (Real.exp_pos _).le
  have hA0 : 0 ≤ eA := by rw [← heA]; exact (Real.exp_pos _).le
  have hG0 : 0 ≤ eG := by rw [← heG]; exact (Real.exp_pos _).le
  have hχA0 : 0 ≤ eχA := by rw [← heχA]; exact (Real.exp_pos _).le
  have hχG0 : 0 ≤ eχG := by rw [← heχG]; exact (Real.exp_pos _).le
  have hx : 0 ≤ ‖T‖ := norm_nonneg _
  have hy : 0 ≤ ‖w‖ := norm_nonneg _
  -- the pieces
  have g4a : ‖multOp D.Pl D.K (D.level n) a1‖ ≤ C4 * (D.level n).ν⁻¹ ^ k4 * eA * ‖T‖ := by
    rw [ha1, ← heA]; exact f4a T
  have g4b : ‖multOp D.Pl D.K (D.level n) a2‖ ≤ C4 * (D.level n).ν⁻¹ ^ k4 * eG * ‖w‖ := by
    rw [ha2, ← heG, hTw]; exact f4b w
  have g4va : ‖a1‖ ≤ C4v * (D.level n).ν⁻¹ ^ k4v * eχA * ‖T‖ := by
    rw [ha1, ← heχA]; exact f4va T
  have g4vb : ‖a2‖ ≤ C4v * (D.level n).ν⁻¹ ^ k4v * eχG * ‖w‖ := by
    rw [ha2, ← heχG, hTw]; exact f4vb w
  have hb1 : ‖b1‖ ≤ C6 * (D.level n).ν⁻¹ ^ k6 * eA' * ‖T‖ := by
    rw [hb1d, ← heA']; exact f6z T (by rw [hTw]; exact hMn z hz w)
  have hb2 : ‖b2‖ ≤ C5 * (D.level n).ν⁻¹ ^ k5 * eG' * ‖w‖ := by
    rw [hb2d, ← heG', hTw]; exact f5z w
  have hb3 : ‖b3‖ ≤ C7 * (D.level n).ν⁻¹ ^ k7 * eA' * ‖T‖ := by
    rw [hb3d, ← heA']; exact f7z T
  have hk1 : k4 ≤ k4 + k4v + kB + k5 + k6 + k7 := by omega
  have hk2 : k4v ≤ k4 + k4v + kB + k5 + k6 + k7 := by omega
  have hk3 : kB + k6 ≤ k4 + k4v + kB + k5 + k6 + k7 := by omega
  have hk4 : kB + k5 ≤ k4 + k4v + kB + k5 + k6 + k7 := by omega
  have hk5 : kB + k7 ≤ k4 + k4v + kB + k5 + k6 + k7 := by omega
  -- stress bounds
  have sM1 := g4a.trans (ef_term (K := k4 + k4v + kB + k5 + k6 + k7) hν hν1' hk1 hA0 le_rfl hx)
  have sM2 := g4b.trans (ef_term (K := k4 + k4v + kB + k5 + k6 + k7) hν hν1' hk1 hG0 le_rfl hy)
  have sM3 := ef_term2 hν hν1' hk3 hA'0 hA'A hx hb1 (fBz b1).1 (norm_nonneg _)
  have sM4 := ef_term2 hν hν1' hk4 hG'0 hG'G hy hb2 (fBz b2).1 (norm_nonneg _)
  have sM5 := ef_term2 hν hν1' hk5 hA'0 hA'A hx hb3 (fBz b3).1 (norm_nonneg _)
  -- velocity bounds
  have sV1 := g4va.trans (ef_term (K := k4 + k4v + kB + k5 + k6 + k7) hν hν1' hk2 hχA0 le_rfl hx)
  have sV2 := g4vb.trans (ef_term (K := k4 + k4v + kB + k5 + k6 + k7) hν hν1' hk2 hχG0 le_rfl hy)
  have sV3 := ef_term2 hν hν1' hk3 hA'0 hA'χ hx hb1 (fBz b1).2 (norm_nonneg _)
  have sV4 := ef_term2 hν hν1' hk4 hG'0 hG'χ hy hb2 (fBz b2).2 (norm_nonneg _)
  have sV5 := ef_term2 hν hν1' hk5 hA'0 hA'χ hx hb3 (fBz b3).2 (norm_nonneg _)
  -- triangle inequalities
  have tM : ‖multOp D.Pl D.K (D.level n) (ageVel D.Pl D.K (D.level n) (D.mu n z) T +
        Rop D.Pl (D.level n) (D.mu n z) ((wardOps D.Pl D.K (D.level n) (D.mu n z)).2.2 T -
          EAOp D.K (D.level n) (D.mu n z) (LjOp D.Pl D.K (D.level n) (D.mu n z) T) -
          rAOp D.Pl D.K (D.level n) (D.mu n z) (LjOp D.Pl D.K (D.level n) (D.mu n z) T)))‖ ≤
      ‖multOp D.Pl D.K (D.level n) a1‖ + ‖multOp D.Pl D.K (D.level n) a2‖ +
        (‖multOp D.Pl D.K (D.level n) (Rop D.Pl (D.level n) (D.mu n z) b1)‖ +
          ‖multOp D.Pl D.K (D.level n) (Rop D.Pl (D.level n) (D.mu n z) b2)‖ +
          ‖multOp D.Pl D.K (D.level n) (Rop D.Pl (D.level n) (D.mu n z) b3)‖) := by
    rw [hvQ]
    simp only [map_add, map_sub]
    refine (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) ?_)
    exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  have tV : ‖ageVel D.Pl D.K (D.level n) (D.mu n z) T +
        Rop D.Pl (D.level n) (D.mu n z) ((wardOps D.Pl D.K (D.level n) (D.mu n z)).2.2 T -
          EAOp D.K (D.level n) (D.mu n z) (LjOp D.Pl D.K (D.level n) (D.mu n z) T) -
          rAOp D.Pl D.K (D.level n) (D.mu n z) (LjOp D.Pl D.K (D.level n) (D.mu n z) T))‖ ≤
      ‖a1‖ + ‖a2‖ + (‖Rop D.Pl (D.level n) (D.mu n z) b1‖ +
        ‖Rop D.Pl (D.level n) (D.mu n z) b2‖ + ‖Rop D.Pl (D.level n) (D.mu n z) b3‖) := by
    rw [hvQ]
    simp only [map_add, map_sub]
    refine (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) ?_)
    exact (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  -- collect
  have hP : 0 ≤ (D.level n).ν⁻¹ ^ (k4 + k4v + kB + k5 + k6 + k7) :=
    pow_nonneg (inv_nonneg.2 hν.le) _
  have hU : 0 ≤ (D.level n).ν⁻¹ ^ (k4 + k4v + kB + k5 + k6 + k7) * eA * ‖T‖ :=
    mul_nonneg (mul_nonneg hP hA0) hx
  have hW : 0 ≤ (D.level n).ν⁻¹ ^ (k4 + k4v + kB + k5 + k6 + k7) * eG * ‖w‖ :=
    mul_nonneg (mul_nonneg hP hG0) hy
  have hU' : 0 ≤ (D.level n).ν⁻¹ ^ (k4 + k4v + kB + k5 + k6 + k7) * eχA * ‖T‖ :=
    mul_nonneg (mul_nonneg hP hχA0) hx
  have hW' : 0 ≤ (D.level n).ν⁻¹ ^ (k4 + k4v + kB + k5 + k6 + k7) * eχG * ‖w‖ :=
    mul_nonneg (mul_nonneg hP hχG0) hy
  have c0 : 0 ≤ |C4| := abs_nonneg _
  have c1 : 0 ≤ |C4v| := abs_nonneg _
  have c2 : 0 ≤ |CB| * |C5| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have c3 : 0 ≤ |CB| * |C6| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have c4 : 0 ≤ |CB| * |C7| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have keyM : ‖multOp D.Pl D.K (D.level n) (ageVel D.Pl D.K (D.level n) (D.mu n z) T +
        Rop D.Pl (D.level n) (D.mu n z) ((wardOps D.Pl D.K (D.level n) (D.mu n z)).2.2 T -
          EAOp D.K (D.level n) (D.mu n z) (LjOp D.Pl D.K (D.level n) (D.mu n z) T) -
          rAOp D.Pl D.K (D.level n) (D.mu n z) (LjOp D.Pl D.K (D.level n) (D.mu n z) T)))‖ ≤
      (|C4| + |C4v| + (|CB| * |C5| + |CB| * |C6| + |CB| * |C7|)) *
          (D.level n).ν⁻¹ ^ (k4 + k4v + kB + k5 + k6 + k7) * eA * ‖T‖ +
        (|C4| + |C4v| + (|CB| * |C5| + |CB| * |C6| + |CB| * |C7|)) *
          (D.level n).ν⁻¹ ^ (k4 + k4v + kB + k5 + k6 + k7) * eG * ‖w‖ := by
    linarith [tM, sM1, sM2, sM3, sM4, sM5, mul_nonneg c1 hU, mul_nonneg c2 hU,
      mul_nonneg c1 hW, mul_nonneg c3 hW, mul_nonneg c4 hW]
  have keyV : ‖ageVel D.Pl D.K (D.level n) (D.mu n z) T +
        Rop D.Pl (D.level n) (D.mu n z) ((wardOps D.Pl D.K (D.level n) (D.mu n z)).2.2 T -
          EAOp D.K (D.level n) (D.mu n z) (LjOp D.Pl D.K (D.level n) (D.mu n z) T) -
          rAOp D.Pl D.K (D.level n) (D.mu n z) (LjOp D.Pl D.K (D.level n) (D.mu n z) T))‖ ≤
      (|C4| + |C4v| + (|CB| * |C5| + |CB| * |C6| + |CB| * |C7|)) *
          (D.level n).ν⁻¹ ^ (k4 + k4v + kB + k5 + k6 + k7) * eχA * ‖T‖ +
        (|C4| + |C4v| + (|CB| * |C5| + |CB| * |C6| + |CB| * |C7|)) *
          (D.level n).ν⁻¹ ^ (k4 + k4v + kB + k5 + k6 + k7) * eχG * ‖w‖ := by
    linarith [tV, sV1, sV2, sV3, sV4, sV5, mul_nonneg c0 hU', mul_nonneg c2 hU',
      mul_nonneg c0 hW', mul_nonneg c3 hW', mul_nonneg c4 hW']
  rw [← heA, ← heG] at keyM
  rw [← heχA, ← heχG] at keyV
  exact ⟨keyM, keyV⟩


end UnforcedLeray.Short.PartIIIb.Concrete
