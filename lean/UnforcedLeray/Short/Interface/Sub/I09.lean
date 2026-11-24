import UnforcedLeray.Loc.AssemblyB
import UnforcedLeray.Short.Interface.Statements

/-!
# Interface:I09 (helper 2b-4), decomposition: the periodic transfer of the Leray coupling

Source of record: `the November 2 reference manuscript`, lines 173-180 (the mode
equation `loc:eq:mode` in `𝒟'(ℝ³ × ℝ/𝒯ℤ)`, whose pairing with the Leray projection is the term
`𝔓 div(U_* ⊗ b_* + b_* ⊗ U_*)`) and the energy class `b_* ∈ 𝒴_{2,div}`, `∇b_* ∈ 𝒴₂` (lines
167-170). `PeriodicCouplingTransfer` (Statements.lean) asks for
`∫_ℝ weakCoupling V b ψ = ∫_{(0,P]} projectedCoupling V b (periodizeTest P ψ)` for `b ∈ 𝒴₂`
(not necessarily `H¹`) and a regular background `V`.


* additivity of the literal pairing `lerayDivPairing` in the test (`leaf2_lerayDivPairing_sum`);
* at each phase `τ ∈ (0, P]` the periodization of a similarity test, paired with the columns, is
  the finite sum of the pairings at the phases `τ + kP` (`leaf2_periodize_eq`);
* the unfolding of `∫_ℝ F` into `∑ₖ ∫_{(0,P]} F(· + kP)` for integrable `F` vanishing at
  large phases (`leaf2_integral_translates`, via `IsAddFundamentalDomain.integral_eq_tsum''`).

What remains is one analytic fact, the integrability of the line coupling
`τ ↦ weakCoupling V b ψ τ` for `b ∈ 𝒴₂` (`WeakCouplingIntegrableY2`; the `H¹` form is the last
clause of Interface:I10 and follows from it since `IsH1Periodic` gives `𝒴₂`). It is reduced here
to three sub-lemmas, each a Prop below:

* `SymColumnsIsY2`: the columns of `V⊗b + b⊗V` are in `𝒴₂` (`V` bounded and jointly measurable,
  `b ∈ 𝒴₂`);
* `LerayFiberIdentity`: for `c ∈ L²(ℝ³)` and a representative `pc` of `𝔓c`, the fiber integral
  `∫⟨c, 𝔓∂ⱼφ⟩ = ∫⟨pc, ∂ⱼφ⟩` (self-adjointness of `𝔓`);
* `SimilarityPartialPhaseTest`: `(τ,y) ↦ ∂ⱼψ(τ, y)` is a phase test with a time window.

`weakCouplingIntegrableY2_of` proves the integrability from them (projected representative
`exists_projected_rep`, the unfolding `B0005.IsY2.pairTerm_unfold`, and Fubini
`Integrable.integral_prod_left`), and `periodicCouplingTransfer_of` assembles the transfer.
-/

set_option autoImplicit false

open Set MeasureTheory Filter
open scoped ENNReal ContDiff Topology

namespace UnforcedLeray.Short.Interface

open UnforcedLeray UnforcedLeray.Blueprint UnforcedLeray.Cons.C08

/-! ## 0. The three analytic sub-lemmas -/

/-- **Sub-lemma I09/1** (the columns of the coupling stress are `𝒴₂`, source lines 167-180: for
bounded continuous `U_*` and `b_* ∈ 𝒴₂` the columns of `U_*⊗b_* + b_*⊗U_*` are periodic, jointly
measurable and square integrable on the period slab). -/
def SymColumnsIsY2 : Prop :=
  ∀ (P : ℝ) (V : ℝ → SpatialField) (dV : Fin 3 → ℝ → SpatialField) (b : ℝ → SpatialField),
    0 < P → IsL3Background P V dV → B0005.IsY2 P b → ∀ j : Fin 3,
      B0005.IsY2 P (fun τ => symTensorColumns (V τ) (b τ) j)

/-- **Sub-lemma I09/2** (the pairing against `𝔓∂ⱼφ` moves onto a representative of `𝔓c`, source
lines 173-180: `𝔓` is the Leray projection, an orthogonal projection of `L²(ℝ³; ℝ³)`, hence
self-adjoint). For `c ∈ L²`, a representative `pc =ᵃᵉ 𝔓c`, and a vector test `φ`:
`∫ ⟨c, 𝔓∂ⱼφ⟩ = ∫ ⟨pc, ∂ⱼφ⟩`. -/
def LerayFiberIdentity : Prop :=
  ∀ (c pc : SpatialField) (φ : Space → Space) (j : Fin 3),
    MemLp c 2 volume → IsVectorTest φ →
      pc =ᵐ[volume] (⇑(Leray.projection (toL2 c)) : SpatialField) →
        (∫ y, inner ℝ (c y) (projectedPartial φ j y)) =
          ∫ y, inner ℝ (pc y) (testPartial φ j y)

/-- **Sub-lemma I09/3** (a spatial derivative of a similarity test is a phase test with a time
window: `ψ` is smooth with compact support, so is `(τ,y) ↦ ∂ⱼψ(τ,y)`). -/
def SimilarityPartialPhaseTest : Prop :=
  ∀ ψ : SpaceTime → Space, IsSimilarityTest ψ → ∀ j : Fin 3,
    ∃ R : ℝ, 0 ≤ R ∧ ∃ χ : ℝ × Space → Space,
      UnforcedLeray.PhaseSpace.IsPhaseTest 0 χ ∧
      UnforcedLeray.PhaseTrace.TimeSupp (-R) R χ ∧
      ∀ (τ : ℝ) (y : Space), χ (τ, y) = testPartial (slice ψ τ) j y

/-- The integrability of the line coupling for `b ∈ 𝒴₂` on a regular background: the shape of
the last clause of Interface:I10 (`ModeSolutionIntegrability`), in the `𝒴₂` form that
`PeriodicCouplingTransfer` requires. -/
def WeakCouplingIntegrableY2 : Prop :=
  ∀ (P : ℝ) (V : ℝ → SpatialField) (dV : Fin 3 → ℝ → SpatialField) (b : ℝ → SpatialField),
    0 < P → IsL3Background P V dV → B0005.IsY2 P b → ∀ ψ : SpaceTime → Space,
      IsSimilarityTest ψ → Integrable (weakCoupling V b ψ)

namespace I09

/-! ## 1. Additivity of the literal pairing in the test -/

theorem leaf2_toL2_zero : toL2 (0 : SpatialField) = 0 := by
  rw [toL2_of_memLp (MemLp.zero : MemLp (0 : SpatialField) 2 volume)]
  exact MemLp.toLp_zero _

theorem leaf2_toL2_add {f g : SpatialField} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    toL2 (f + g) = toL2 f + toL2 g := by
  rw [toL2_of_memLp (hf.add hg), toL2_of_memLp hf, toL2_of_memLp hg]
  exact hf.toLp_add hg

theorem leaf2_toL2_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → SpatialField) :
    (∀ i ∈ s, MemLp (f i) 2 volume) →
      toL2 (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, toL2 (f i) := by
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simp only [Finset.sum_empty]
    exact leaf2_toL2_zero
  | @insert a s ha ih =>
    intro hf
    have h1 : MemLp (f a) 2 volume := hf a (Finset.mem_insert_self a s)
    have h2 : ∀ i ∈ s, MemLp (f i) 2 volume := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hs : MemLp (fun x => ∑ i ∈ s, f i x) 2 volume := memLp_finsetSum s h2
    have e : (fun x => ∑ i ∈ insert a s, f i x) = f a + (fun x => ∑ i ∈ s, f i x) := by
      funext x
      simp only [Finset.sum_insert ha, Pi.add_apply]
    rw [e, Finset.sum_insert ha, leaf2_toL2_add h1 hs, ih h2]

/-- Linearity of `∂_j` over a finite sum of vector tests. -/
theorem leaf2_testPartial_sum {ι : Type*} (s : Finset ι) (φ : ι → Space → Space)
    (hφ : ∀ i ∈ s, IsVectorTest (φ i)) (j : Fin 3) :
    testPartial (fun y => ∑ i ∈ s, φ i y) j = fun y => ∑ i ∈ s, testPartial (φ i) j y := by
  funext y
  have hd : ∀ i ∈ s, DifferentiableAt ℝ (φ i) y := fun i hi =>
    ((hφ i hi).smooth.differentiable (by simp)).differentiableAt
  show fderiv ℝ (fun y => ∑ i ∈ s, φ i y) y (coordinateVector j) =
    ∑ i ∈ s, fderiv ℝ (φ i) y (coordinateVector j)
  have e : (fun y => ∑ i ∈ s, φ i y) = ∑ i ∈ s, φ i :=
    funext fun z => (Finset.sum_apply z s φ).symm
  rw [e, fderiv_sum hd, ContinuousLinearMap.sum_apply]

/-- The literal pairing `lerayDivPairing` is additive in the test. -/
theorem leaf2_lerayDivPairing_sum {ι : Type*} [DecidableEq ι] (col : Fin 3 → SpatialField)
    (s : Finset ι) (φ : ι → Space → Space) (hφ : ∀ i ∈ s, IsVectorTest (φ i)) :
    lerayDivPairing col (fun y => ∑ i ∈ s, φ i y) = ∑ i ∈ s, lerayDivPairing col (φ i) := by
  have hj : ∀ j : Fin 3, toL2 (testPartial (fun y => ∑ i ∈ s, φ i y) j) =
      ∑ i ∈ s, toL2 (testPartial (φ i) j) := fun j => by
    rw [leaf2_testPartial_sum s φ hφ j]
    exact leaf2_toL2_sum s (fun i => testPartial (φ i) j)
      (fun i hi => UnforcedLeray.Blueprint.L13.testPartial_memLp (hφ i hi) j)
  unfold lerayDivPairing
  simp only [hj, map_sum, inner_sum, Finset.sum_neg_distrib]
  congr 1
  exact Finset.sum_comm

/-- The literal pairing vanishes on the zero test. -/
theorem leaf2_lerayDivPairing_zero (col : Fin 3 → SpatialField) : lerayDivPairing col 0 = 0 := by
  have h : ∀ j : Fin 3, testPartial (0 : Space → Space) j = 0 := fun j => by
    funext y
    simp [testPartial, Pi.zero_def]
  unfold lerayDivPairing
  simp [h, leaf2_toL2_zero]

/-! ## 2. Support and slices of a similarity test -/

/-- A similarity test vanishes for large `|τ|`, uniformly in `y`. -/
theorem leaf2_support {ψ : SpaceTime → Space} (hψ : IsSimilarityTest ψ) :
    ∃ R : ℝ, ∀ (t : ℝ) (y : Space), R < |t| → ψ (t, y) = 0 := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : SpaceTime)).1
    hψ.compact.isCompact.isBounded
  refine ⟨R, fun t y ht => ?_⟩
  by_contra hne
  have hmem : ((t, y) : SpaceTime) ∈ tsupport ψ :=
    subset_tsupport ψ (Function.mem_support.2 hne)
  have h1 := hR hmem
  rw [Metric.mem_closedBall, dist_zero_right] at h1
  have h2 : ‖t‖ ≤ ‖((t, y) : SpaceTime)‖ := by
    rw [Prod.norm_def]
    exact le_max_left _ _
  rw [Real.norm_eq_abs] at h2
  linarith

/-- A phase slice of a similarity test is a vector test. -/
theorem leaf2_slice_isVectorTest {ψ : SpaceTime → Space} (hψ : IsSimilarityTest ψ) (t : ℝ) :
    IsVectorTest (slice ψ t) := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : SpaceTime)).1
    hψ.compact.isCompact.isBounded
  have hs : ContDiff ℝ ∞ (fun y : Space => ψ (t, y)) :=
    hψ.smooth.comp (contDiff_const.prodMk contDiff_id)
  refine ⟨hs, HasCompactSupport.intro (isCompact_closedBall (0 : Space) R) (fun y hy => ?_)⟩
  by_contra hne
  have hmem : ((t, y) : SpaceTime) ∈ tsupport ψ :=
    subset_tsupport ψ (Function.mem_support.2 hne)
  have h1 := hR hmem
  rw [Metric.mem_closedBall, dist_zero_right] at h1
  have h2 : ‖y‖ ≤ ‖((t, y) : SpaceTime)‖ := by
    rw [Prod.norm_def]
    exact le_max_right _ _
  exact hy (by rw [Metric.mem_closedBall, dist_zero_right]; linarith)

/-- For `τ ∈ (0, P]`, the phases `τ + kP` with `k` outside a fixed window `[-N, N]` carry no
support of a test vanishing beyond `|t| > R`, once `R + P < NP`. -/
theorem leaf2_abs_add_mul_gt {P R τ : ℝ} {N : ℕ} (hP : 0 < P) (hN : R + P < (N : ℝ) * P)
    (hτ : τ ∈ Ioc (0 : ℝ) P) (k : ℤ) (hk : k ∉ Finset.Icc (-(N : ℤ)) N) :
    R < |τ + (k : ℝ) * P| := by
  obtain ⟨hτ0, hτP⟩ := hτ
  have hk' : (N : ℤ) + 1 ≤ k ∨ k + 1 ≤ -(N : ℤ) := by
    by_contra hcon
    push_neg at hcon
    exact hk (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  rcases hk' with h | h
  · have hkR : (N : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast h
    have h1 : ((N : ℝ) + 1) * P ≤ (k : ℝ) * P := mul_le_mul_of_nonneg_right hkR hP.le
    have h2 : ((N : ℝ) + 1) * P = (N : ℝ) * P + P := by ring
    have h3 : R < τ + (k : ℝ) * P := by linarith
    exact lt_of_lt_of_le h3 (le_abs_self _)
  · have hkR : (k : ℝ) + 1 ≤ -(N : ℝ) := by exact_mod_cast h
    have h1 : (k : ℝ) * P ≤ (-(N : ℝ) - 1) * P :=
      mul_le_mul_of_nonneg_right (by linarith) hP.le
    have h2 : (-(N : ℝ) - 1) * P = -((N : ℝ) * P) - P := by ring
    have h3 : R < -(τ + (k : ℝ) * P) := by linarith
    exact lt_of_lt_of_le h3 (neg_le_abs _)

/-! ## 3. The periodization at a phase is a finite sum of translates -/

/-- At a phase `τ ∈ (0, P]`, the periodization of `ψ` tested against the Leray pairing is the
finite sum over `|k| ≤ N` of the unperiodized pairings at the phases `τ + kP`, by periodicity
of `V` and `b`. -/
theorem leaf2_periodize_eq (V b : ℝ → SpatialField) {P : ℝ} (hVp : Function.Periodic V P)
    (hbp : Function.Periodic b P) {ψ : SpaceTime → Space} (hψ : IsSimilarityTest ψ) {R : ℝ}
    (hR : ∀ (t : ℝ) (y : Space), R < |t| → ψ (t, y) = 0) {N : ℕ} (hP : 0 < P)
    (hN : R + P < (N : ℝ) * P) {τ : ℝ} (hτ : τ ∈ Ioc (0 : ℝ) P) :
    projectedCoupling V b (periodizeTest P ψ) τ =
      ∑ k ∈ Finset.Icc (-(N : ℤ)) N, projectedCoupling V b ψ (τ + (k : ℝ) * P) := by
  have hslice : slice (periodizeTest P ψ) τ =
      fun y => ∑ k ∈ Finset.Icc (-(N : ℤ)) N, slice ψ (τ + (k : ℝ) * P) y := by
    funext y
    show (∑ᶠ k : ℤ, ψ (τ + (k : ℝ) * P, y)) =
      ∑ k ∈ Finset.Icc (-(N : ℤ)) N, ψ (τ + (k : ℝ) * P, y)
    apply finsum_eq_sum_of_support_subset
    intro k hk
    apply Finset.mem_coe.2
    by_contra hkT
    exact Function.mem_support.1 hk (hR _ y (leaf2_abs_add_mul_gt hP hN hτ k hkT))
  unfold projectedCoupling
  rw [hslice]
  refine (leaf2_lerayDivPairing_sum _ _ (fun k : ℤ => slice ψ (τ + (k : ℝ) * P))
    (fun k _ => leaf2_slice_isVectorTest hψ _)).trans ?_
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [hVp.int_mul k τ, hbp.int_mul k τ]

/-! ## 4. Unfolding the integral over `ℝ` into the period cell -/

/-- The lattice `ℤ ≃ zmultiples P` for `P > 0`. -/
noncomputable def leaf2_zmEquiv {P : ℝ} (hP : 0 < P) : ℤ ≃ AddSubgroup.zmultiples P :=
  Equiv.ofBijective (fun n => ⟨n • P, n, rfl⟩) ⟨fun m n h => by
    have h' : m • P = n • P := congrArg Subtype.val h
    have h1 : (m : ℝ) * P = (n : ℝ) * P := by simpa [zsmul_eq_mul] using h'
    exact_mod_cast mul_right_cancel₀ hP.ne' h1, fun g => by
      obtain ⟨g, n, rfl⟩ := g
      exact ⟨n, rfl⟩⟩

theorem leaf2_zmEquiv_val {P : ℝ} (hP : 0 < P) (n : ℤ) :
    ((leaf2_zmEquiv hP n : AddSubgroup.zmultiples P) : ℝ) = (n : ℝ) * P := by
  show (n • P : ℝ) = (n : ℝ) * P
  rw [zsmul_eq_mul]

theorem leaf2_zmEquiv_vadd {P : ℝ} (hP : 0 < P) (n : ℤ) (x : ℝ) :
    (leaf2_zmEquiv hP n) +ᵥ x = x + (n : ℝ) * P := by
  rw [AddSubgroup.vadd_def, vadd_eq_add, leaf2_zmEquiv_val hP n, add_comm]

/-- The integral over `ℝ` of a summable-in-translates function is the sum over the finitely
many nonvanishing translates, each integrated over the period cell `(0, P]`. -/
theorem leaf2_integral_translates {P : ℝ} (hP : 0 < P) {F : ℝ → ℝ} (hF : Integrable F)
    {N : ℕ} (hzero : ∀ τ ∈ Ioc (0 : ℝ) P, ∀ k : ℤ, k ∉ Finset.Icc (-(N : ℤ)) N →
      F (τ + (k : ℝ) * P) = 0) :
    ∫ τ, F τ = ∑ k ∈ Finset.Icc (-(N : ℤ)) N, ∫ τ in Ioc (0 : ℝ) P, F (τ + (k : ℝ) * P) := by
  have hfd := isAddFundamentalDomain_Ioc hP 0 volume
  rw [zero_add] at hfd
  rw [hfd.integral_eq_tsum'' F hF, ← (leaf2_zmEquiv hP).tsum_eq]
  rw [tsum_eq_sum (s := Finset.Icc (-(N : ℤ)) N) ?_]
  · refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [leaf2_zmEquiv_vadd]
  · intro k hk
    have hz : ∀ x ∈ Ioc (0 : ℝ) P, F ((leaf2_zmEquiv hP k) +ᵥ x) = 0 := fun x hx => by
      rw [leaf2_zmEquiv_vadd]
      exact hzero x hx k hk
    exact setIntegral_eq_zero_of_forall_eq_zero hz


/-! ## 5. The conditional periodic transfer -/

/-- **Interface:I09, conditional form.** `PeriodicCouplingTransfer` follows from the
integrability of the line coupling. -/
theorem periodicCouplingTransfer_of_integrable (hint : WeakCouplingIntegrableY2) :
    PeriodicCouplingTransfer := by
  unfold PeriodicCouplingTransfer
  intro P V dV b hP hV hb ψ hψ
  obtain ⟨C, hC⟩ := hV.bounded
  have hae : (fun τ => weakCoupling V b ψ τ) =ᵐ[volume] fun τ => projectedCoupling V b ψ τ := by
    filter_upwards [UnforcedLeray.Cons.C08.ae_memLp_slice hP hb.periodic hb.memL2] with τ hτ
    exact lerayDivIntegral_eq_lerayDivPairing
      (UnforcedLeray.Cons.C08.columnsL2_symTensor (hV.continuous τ) (fun x => hC τ x) hτ)
      (slice ψ τ)
  have hint' : Integrable (fun τ => projectedCoupling V b ψ τ) :=
    (hint P V dV b hP hV hb ψ hψ).congr hae
  obtain ⟨R, hR⟩ := leaf2_support hψ
  obtain ⟨N, hN0⟩ := exists_nat_gt ((R + P) / P)
  have hN : R + P < (N : ℝ) * P := (div_lt_iff₀ hP).1 hN0
  have hFzero : ∀ (t : ℝ), R < |t| → projectedCoupling V b ψ t = 0 := by
    intro t ht
    have hs : slice ψ t = 0 := funext fun y => hR t y ht
    unfold projectedCoupling
    rw [hs, leaf2_lerayDivPairing_zero]
  have hzero : ∀ τ ∈ Ioc (0 : ℝ) P, ∀ k : ℤ, k ∉ Finset.Icc (-(N : ℤ)) N →
      projectedCoupling V b ψ (τ + (k : ℝ) * P) = 0 :=
    fun τ hτ k hk => hFzero _ (leaf2_abs_add_mul_gt hP hN hτ k hk)
  calc (∫ τ, weakCoupling V b ψ τ)
      = ∫ τ, projectedCoupling V b ψ τ := integral_congr_ae hae
    _ = ∑ k ∈ Finset.Icc (-(N : ℤ)) N,
          ∫ τ in Ioc (0 : ℝ) P, projectedCoupling V b ψ (τ + (k : ℝ) * P) :=
        leaf2_integral_translates hP hint' hzero
    _ = ∫ τ in Ioc (0 : ℝ) P,
          ∑ k ∈ Finset.Icc (-(N : ℤ)) N, projectedCoupling V b ψ (τ + (k : ℝ) * P) :=
        (integral_finsetSum (Finset.Icc (-(N : ℤ)) N)
          (fun k _ => (hint'.comp_add_right ((k : ℝ) * P)).integrableOn)).symm
    _ = ∫ τ in Ioc (0 : ℝ) P, projectedCoupling V b (periodizeTest P ψ) τ :=
        setIntegral_congr_fun measurableSet_Ioc
          (fun τ hτ => (leaf2_periodize_eq V b hV.periodic hb.periodic hψ hR hP hN hτ).symm)

end I09

/-! ## 6. Integrability of the line coupling from the three sub-lemmas -/

/-- **The integrability of the line coupling for `b ∈ 𝒴₂`, from the three sub-lemmas.** Let
`c_j(τ) = (V⊗b + b⊗V)_{·j}(τ) ∈ 𝒴₂` (sub-lemma 1) with projected representative `pc_j ∈ 𝒴₂`
(`exists_projected_rep`). For almost every phase `τ`, `weakCoupling V b ψ τ` is
`-∑ⱼ ∫ ⟨pc_j τ, ∂ⱼψ(τ)⟩` (`columnsL2_symTensor` and sub-lemma 2); and `∂ⱼψ` is a phase test with a
time window (sub-lemma 3), so `pairTerm pc_j (∂ⱼψ)` is integrable on `ℝ × ℝ³`
(`B0005.IsY2.pairTerm_unfold`), whence its fiber integral is integrable in `τ` (Fubini). -/
theorem weakCouplingIntegrableY2_of (h₁ : SymColumnsIsY2) (h₂ : LerayFiberIdentity)
    (h₃ : SimilarityPartialPhaseTest) : WeakCouplingIntegrableY2 := by
  intro P V dV b hP hV hb ψ hψ
  have hFact : Fact (0 < P) := ⟨hP⟩
  have hcol : ∀ j : Fin 3, B0005.IsY2 P (fun τ => symTensorColumns (V τ) (b τ) j) :=
    h₁ P V dV b hP hV hb
  choose pc hpc hpcae using fun j : Fin 3 =>
    UnforcedLeray.Cons.C08.exists_projected_rep hP (hcol j)
  obtain ⟨C, hC⟩ := hV.bounded
  have hint : ∀ j : Fin 3, Integrable (fun τ => ∫ y, inner ℝ (pc j τ y)
      (testPartial (slice ψ τ) j y)) := by
    intro j
    obtain ⟨R, hR0, χ, hχ, hχR, hχe⟩ := h₃ ψ hψ j
    have h1 : Integrable (pairTerm (pc j) χ) :=
      ((hpc j).pairTerm_unfold hχ (by linarith) hχR).1
    have h2 : Integrable (fun τ => ∫ y, pairTerm (pc j) χ (τ, y)) := by
      rw [Measure.volume_eq_prod] at h1
      exact h1.integral_prod_left
    refine h2.congr (Eventually.of_forall fun τ => ?_)
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [pairTerm, hχe]
  have hae : ∀ᵐ τ, weakCoupling V b ψ τ =
      -∑ j : Fin 3, ∫ y, inner ℝ (pc j τ y) (testPartial (slice ψ τ) j y) := by
    filter_upwards [UnforcedLeray.Cons.C08.ae_memLp_slice hP hb.periodic hb.memL2,
      ae_all_iff.2 hpcae] with τ hτ hτj
    unfold weakCoupling lerayDivIntegral
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    exact h₂ (symTensorColumns (V τ) (b τ) j) (pc j τ) (slice ψ τ) j
      (UnforcedLeray.Cons.C08.columnsL2_symTensor (hV.continuous τ) (fun x => hC τ x) hτ j)
      (I09.leaf2_slice_isVectorTest hψ τ) (hτj j)
  have hsum : Integrable (fun τ => -∑ j : Fin 3, ∫ y, inner ℝ (pc j τ y)
      (testPartial (slice ψ τ) j y)) :=
    (integrable_finsetSum _ fun j _ => hint j).neg
  exact hsum.congr (hae.mono fun τ h => h.symm)

/-- **Interface:I09, conditional on the three sub-lemmas.** The transfer of the Leray coupling
from the line to one period. The unconditional `periodicCouplingTransfer` (task `Interface:I09`,
`Short/Interface/Leaf2_Coupling.lean`) applies this to the proved sub-lemmas
(tasks `Interface:I09/1`, `I09/2`, `I09/3`). -/
theorem periodicCouplingTransfer_of (h₁ : SymColumnsIsY2) (h₂ : LerayFiberIdentity)
    (h₃ : SimilarityPartialPhaseTest) : PeriodicCouplingTransfer :=
  I09.periodicCouplingTransfer_of_integrable (weakCouplingIntegrableY2_of h₁ h₂ h₃)

end UnforcedLeray.Short.Interface
