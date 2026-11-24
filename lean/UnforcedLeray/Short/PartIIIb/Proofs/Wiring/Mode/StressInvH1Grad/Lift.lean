import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.Inverses.Level
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Defs
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Proofs.CartLiftIsTest.Basic
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Sub.T8_1
import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_6.Pointwise
import UnforcedLeray.Short.PartIIa.Sub.PartIIa_N01_6.ChartPhase
import UnforcedLeray.Short.PartIIa.Sub.N01.CartLiftRows
import UnforcedLeray.Short.PartIIa.StatementsFree
import UnforcedLeray.Short.PartIIb.Bridge.Rep
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradWeak.GLRot.PairLinR.Integrable

/-!
# The physical stress `𝒩_T(T₁ + T₂)` as an element of `Y_2(Sym_3)`

Helper for `Proofs/Wiring/Mode/StressInvH1Grad.lean` (source 1533-1572: tensor forces in
`Y_2(Sym_3)`, `free:weak-stress`; 1644-1648: "`T ↦ sT` multiplies norms by `√π R`"; 2683:
`𝒩_T T = sT`).

* `isInYr_rowsOf_strPhys`: the rows of `strPhys ε⁻¹ c g` lie in `Y_2` of period `P = 2εc` for a
  measurable chart tensor `g ∈ L²(s^{-1/2} dς)` (the pointwise Frobenius identity
  `N01.slabFrobPointwise` and the change of variables `N01.chartPhaseFrob`);
* `memLp_strSum`: `T₁ + T₂ ∈ L²(s^{-1/2} dς)` for a gain-normed stress `T` (`zsum_zOfStr`,
  `Masked.zsumL_ae`);
* `exists_symY2_lift`: a pointwise symmetric field with rows in `Y_2` defines an element of
  `symY2 P` whose tensor pairing `⟨∇Φ, T⟩` is `stressPair`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete.Wiring.ModeAux.StressLiftY

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal ContDiff
open UnforcedLeray.PhaseSpace UnforcedLeray.Axi
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt phaseCell)
open UnforcedLeray.Short.PartIIIb.NearInst (cartLift chartOf nsSym symRZ)

/-- The rows `(T_ij)_j` of a Cartesian real tensor field on `ℝ × ℝ³`, complexified. -/
def rowsOf (Tp : ℝ × Space → Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3) (x : ℝ × Space) : CVec3 :=
  WithLp.toLp 2 fun j => ((Tp x i j : ℝ) : ℂ)

theorem norm_rowsOf_sq (Tp : ℝ × Space → Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3) (x : ℝ × Space) :
    ‖rowsOf Tp i x‖ ^ 2 = ∑ j : Fin 3, (Tp x i j) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [rowsOf, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- `|nsSym T|_F² ≤ ‖T‖²`. -/
theorem frob2_le_normSq (T : Ten3) : UnforcedLeray.Short.PartIIa.N01.frob2 T ≤ ‖T‖ ^ 2 := by
  have hT : ‖T‖ ^ 2 = ∑ p : Fin 3 × Fin 3, (T p) ^ 2 := EuclideanSpace.real_norm_sq_eq T
  have hf : UnforcedLeray.Short.PartIIa.N01.frob2 T =
      T (0, 0) ^ 2 + T (1, 1) ^ 2 + T (2, 2) ^ 2 + 2 * symRZ T ^ 2 := by
    simp [UnforcedLeray.Short.PartIIa.N01.frob2, nsSym, Fin.sum_univ_three]
    ring
  have hsum : ∑ p : Fin 3 × Fin 3, (T p) ^ 2 =
      (T (0, 0)) ^ 2 + (T (0, 1)) ^ 2 + (T (0, 2)) ^ 2 + (T (1, 0)) ^ 2 + (T (1, 1)) ^ 2
        + (T (1, 2)) ^ 2 + (T (2, 0)) ^ 2 + (T (2, 1)) ^ 2 + (T (2, 2)) ^ 2 := by
    rw [Fintype.sum_prod_type]
    simp only [Fin.sum_univ_three]
    ring
  rw [hf, hT, hsum]
  unfold symRZ
  nlinarith [sq_nonneg (T (0, 2) - T (2, 0)), sq_nonneg (T (0, 1)), sq_nonneg (T (1, 0)),
    sq_nonneg (T (1, 2)), sq_nonneg (T (2, 1))]

/-- Pointwise: one row of the lift is bounded by `s² ‖g‖²` at the chart point. -/
theorem norm_rowsOf_strPhys_sq_le (R c : ℝ) (g : Chart → Ten3) (i : Fin 3) (x : ℝ × Space) :
    ‖rowsOf (strPhys R c g) i x‖ ^ 2 ≤
      (chartOf R c x.2 x.1).1 ^ 2 * ‖g (chartOf R c x.2 x.1)‖ ^ 2 := by
  rw [norm_rowsOf_sq]
  have hall := UnforcedLeray.Short.PartIIa.N01.slabFrobPointwise R c g x.1 x.2
  have hle : ∑ j : Fin 3, (strPhys R c g x i j) ^ 2 ≤
      ∑ i' : Fin 3, ∑ j : Fin 3, (cartLift R c g x.1 x.2 i' j) ^ 2 :=
    Finset.single_le_sum (f := fun i' => ∑ j : Fin 3, (cartLift R c g x.1 x.2 i' j) ^ 2)
      (fun i' _ => Finset.sum_nonneg fun j _ => sq_nonneg _) (Finset.mem_univ i)
  refine hle.trans ?_
  rw [hall]
  exact mul_le_mul_of_nonneg_left (frob2_le_normSq _) (sq_nonneg _)

/-- **The rows of the physical tensor lie in `Y_2`** (source 1644-1648, 2683): for a measurable
chart tensor `g ∈ L²(s^{-1/2} dς)`, every row of `strPhys ε⁻¹ c g` is periodic of period
`P = 2εc`, measurable, and of finite phase `L²` norm. -/
theorem isInYr_rowsOf_strPhys {ε c : ℝ} (hε : 0 < ε) (hc : 0 < c) {g : Chart → Ten3}
    (hg : Measurable g) (hL2 : MemLp g 2 (ageμ c (-1 / 2))) (i : Fin 3) :
    UnforcedLeray.Short.IIb.IsInYr (2 * ε * c) 2 (rowsOf (strPhys ε⁻¹ c g) i) := by
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  have hPR : 2 * ε * c = 2 * c / ε⁻¹ := by rw [div_inv_eq_mul]; ring
  refine ⟨Eventually.of_forall fun x => ?_, ?_, ?_⟩
  · have hper : cartLift ε⁻¹ c g (x.1 + 2 * ε * c) x.2 = cartLift ε⁻¹ c g x.1 x.2 := by
      unfold cartLift
      rw [UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.cl_chartOf_period ε c hε hc]
    simp only [rowsOf, strPhys, hper]
  · have hent : ∀ j, Measurable fun x : ℝ × Space => ((strPhys ε⁻¹ c g x i j : ℝ) : ℂ) :=
      fun j => Complex.measurable_ofReal.comp (T8_1.measurable_cartLift_entry ε⁻¹ c g hg i j)
    exact ((PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℂ)).measurable.comp
      (measurable_pi_lambda _ hent)).aestronglyMeasurable
  · set G : Chart → ℝ≥0∞ := fun p => ENNReal.ofReal (‖g p‖ ^ 2) with hGdef
    have hGm : Measurable G := (hg.norm.pow_const 2).ennreal_ofReal
    have hGfin : ∫⁻ p, G p ∂(ageμ c (-1 / 2)) < ⊤ :=
      (hL2.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).lintegral_lt_top
    have hpt : ∀ t : ℝ, ∀ y : Space, ‖rowsOf (strPhys ε⁻¹ c g) i (t, y)‖ₑ ^ (2 : ℝ) ≤
        ENNReal.ofReal ((chartOf ε⁻¹ c y t).1 ^ 2) * G (chartOf ε⁻¹ c y t) := by
      intro t y
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
        Real.rpow_two, hGdef, ← ENNReal.ofReal_mul (sq_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (norm_rowsOf_strPhys_sq_le ε⁻¹ c g i (t, y))
    have hJ : ∫⁻ t in Ioc (0 : ℝ) (2 * ε * c), ∫⁻ y : Space,
        ‖rowsOf (strPhys ε⁻¹ c g) i (t, y)‖ₑ ^ (2 : ℝ) < ⊤ := by
      refine lt_of_le_of_lt (lintegral_mono fun t => lintegral_mono fun y => hpt t y) ?_
      rw [hPR, UnforcedLeray.Short.PartIIa.N01.chartPhaseFrob ε⁻¹ c hR hc G hGm]
      exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
        hGfin
    unfold UnforcedLeray.Short.IIb.phaseLpNorm
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hJ).ne

/-- `strSum T` is measurable (sum of `Lp` representatives). -/
theorem measurable_strSum {c mZ ρb γ ν : ℝ} (T : StrG c mZ ρb γ ν) : Measurable (strSum T) :=
  (Lp.stronglyMeasurable T.fst).measurable.add (Lp.stronglyMeasurable T.snd).measurable

/-- **`T₁ + T₂ ∈ L²(s^{-1/2} dς)`** for a gain-normed stress (source 2698-2700, 3874). -/
theorem memLp_strSum {c mZ ρb γ ν : ℝ} (hν : 0 < ν) (hmZ : 0 ≤ mZ) (hρ : 0 < ρb)
    (T : StrG c mZ ρb γ ν) : MemLp (strSum T) 2 (ageμ c (-1 / 2)) := by
  set F := NearInst.gainEquiv c mZ ρb γ hν (NearInst.strIso c mZ ρb γ ν T)
  exact (Lp.memLp (NearInst.Masked.zsumL c mZ ρb hmZ hρ F)).ae_eq
    ((NearInst.Masked.zsumL_ae c mZ ρb hmZ hρ F).trans (zsum_zOfStr γ hν hρ T))

/-- The physical stress is pointwise symmetric (`cartLift_transpose`). -/
theorem strPhys_symm (R c : ℝ) (g : Chart → Ten3) (x : ℝ × Space) (i j : Fin 3) :
    strPhys R c g x i j = strPhys R c g x j i := by
  have h := congrFun (congrFun
    (UnforcedLeray.Short.PartIIa.N01.cartLift_transpose R c g x.1 x.2) j) i
  simpa [Matrix.transpose_apply, strPhys] using h

/-! ### The lift into `Y_2(Sym_3)` -/

theorem dotL_smul_single_rowsOf (Tp : ℝ × Space → Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3)
    (a : ℂ) (x : ℝ × Space) :
    dotL (a • (EuclideanSpace.single j (1 : ℂ) : CVec3)) (rowsOf Tp i x) = a * (Tp x i j : ℂ) := by
  rw [dotL_apply]
  simp [rowsOf]

theorem isPhaseTest_smul_single {P : ℝ} {φ : ℝ × Space → ℂ} (hφ : IsPhaseTest P φ) (j : Fin 3) :
    IsPhaseTest P (fun p => φ p • (EuclideanSpace.single j (1 : ℂ) : CVec3)) := by
  have h := hφ.clm_comp ((ContinuousLinearMap.id ℝ ℂ).smulRight
    (EuclideanSpace.single j (1 : ℂ) : CVec3))
  simpa using h

/-- The test row `(∂_jΦ_i)_j` of a vector phase test. -/
def gradRow (Φ : ℝ × Space → CVec3) (i : Fin 3) (p : ℝ × Space) : CVec3 :=
  WithLp.toLp 2 fun j => dy j Φ p i

theorem isPhaseTest_gradRow {P : ℝ} {Φ : ℝ × Space → CVec3} (hΦ : IsPhaseTest P Φ) (i : Fin 3) :
    IsPhaseTest P (gradRow Φ i) := by
  have h : gradRow Φ i = ∑ j : Fin 3, fun p =>
      (((EuclideanSpace.proj i : CVec3 →L[ℂ] ℂ).restrictScalars ℝ).smulRight
        (EuclideanSpace.single j (1 : ℂ) : CVec3)) (dy j Φ p) := by
    funext p
    ext k
    simp [gradRow, Pi.single_apply, Finset.sum_apply]
  rw [h]
  exact IsPhaseTest.sum _ fun j _ => (hΦ.dy j).clm_comp _

theorem phaseInt_eq_cell' {P : ℝ} {F : ℝ × Space → ℂ}
    (hF : Integrable F (volume.restrict (phaseCell P))) :
    phaseInt P F = P⁻¹ • ∫ x, F x ∂(volume.restrict (phaseCell P)) := by
  have hprod : (volume : Measure (ℝ × Space)).restrict (phaseCell P) =
      ((volume : Measure ℝ).restrict (Ioc (0 : ℝ) P)).prod (volume : Measure Space) := by
    simpa [phaseCell, Measure.volume_eq_prod] using
      (Measure.restrict_prod_eq_prod_univ (μ := (volume : Measure ℝ))
        (ν := (volume : Measure Space)) (Ioc (0 : ℝ) P)).symm
  rw [hprod] at hF ⊢
  unfold phaseInt
  rw [integral_prod F hF]

theorem phaseInt_sum_cell' {P : ℝ} {F : Fin 3 → ℝ × Space → ℂ}
    (hF : ∀ i, Integrable (F i) (volume.restrict (phaseCell P))) :
    phaseInt P (fun x => ∑ i, F i x) = ∑ i, phaseInt P (F i) := by
  have hint : Integrable (fun x => ∑ i, F i x) (volume.restrict (phaseCell P)) :=
    integrable_finsetSum _ fun i _ => hF i
  rw [phaseInt_eq_cell' hint, integral_finsetSum _ fun i _ => hF i, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => (phaseInt_eq_cell' (hF i)).symm

/-- **The lift into `Y_2(Sym_3)`** (source 1533-1537): a pointwise symmetric real tensor field
whose rows lie in `Y_2` defines `T ∈ symY2 P` with `⟨∇Φ, T⟩ = stressPair P Tp Φ` for every
phase test `Φ`. -/
theorem exists_symY2_lift {P : ℝ} [hP : Fact (0 < P)] (Tp : ℝ × Space → Matrix (Fin 3) (Fin 3) ℝ)
    (hsym : ∀ x i j, Tp x i j = Tp x j i)
    (hrow : ∀ i, UnforcedLeray.Short.IIb.IsInYr P 2 (rowsOf Tp i)) :
    ∃ Ts : UnforcedLeray.Short.PartIIa.symY2 P, ∀ Φ : ℝ × Space → CVec3, IsPhaseTest P Φ →
      UnforcedLeray.Short.PartIIa.tensorGradPair P Φ (Ts : UnforcedLeray.Short.PartIIa.Y2Sym P) =
        stressPair P Tp Φ := by
  have hex : ∀ i, ∃ F : Yq P 2, UnforcedLeray.Short.IIb.HasRepY F (rowsOf Tp i) := fun i => by
    obtain ⟨F, hF, -⟩ := UnforcedLeray.Short.IIb.exists_hasRepY_q P 2 two_pos
      (q := 2) ENNReal.ofNat_ne_top (by norm_num) _ (hrow i)
    exact ⟨F, hF⟩
  choose F hF using hex
  set T0 : UnforcedLeray.Short.PartIIa.Y2Sym P := WithLp.toLp 2 F with hT0
  have hmem : T0 ∈ UnforcedLeray.Short.PartIIa.symY2 P := by
    simp only [UnforcedLeray.Short.PartIIa.symY2, Submodule.mem_iInf, LinearMap.mem_ker]
    intro i j φ
    have hj := isPhaseTest_smul_single φ.2 j
    have hi := isPhaseTest_smul_single φ.2 i
    simp only [UnforcedLeray.Short.PartIIa.symFun, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, PiLp.proj_apply, hT0]
    rw [UnforcedLeray.Short.IIb.phasePair_eq_pairF_of_hasRepY (F i) _ (hF i) hj,
      UnforcedLeray.Short.IIb.phasePair_eq_pairF_of_hasRepY (F j) _ (hF j) hi, sub_eq_zero]
    unfold pairF
    congr 1
    funext x
    rw [dotL_smul_single_rowsOf, dotL_smul_single_rowsOf, hsym x i j]
  refine ⟨⟨T0, hmem⟩, fun Φ hΦ => ?_⟩
  simp only [UnforcedLeray.Short.PartIIa.tensorGradPair, hT0, PiLp.toLp_apply]
  have e1 : ∀ i, phasePair P 2 (fun p => (WithLp.toLp 2 fun j => dy j Φ p i : CVec3)) (F i) =
      pairF P (gradRow Φ i) (rowsOf Tp i) := fun i =>
    UnforcedLeray.Short.IIb.phasePair_eq_pairF_of_hasRepY (F i) _ (hF i)
      (isPhaseTest_gradRow hΦ i)
  simp only [e1]
  have hint : ∀ i, Integrable (fun x => dotL (gradRow Φ i x) (rowsOf Tp i x))
      (volume.restrict (phaseCell P)) := fun i =>
    UnforcedLeray.Short.IIb.integrable_dotL_phaseTest_Yr hP.out one_lt_two
      (isPhaseTest_gradRow hΦ i) (hrow i)
  unfold pairF
  rw [← phaseInt_sum_cell' hint]
  unfold stressPair
  congr 1
  funext x
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dotL_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [gradRow, rowsOf, mul_comm]

end UnforcedLeray.Short.PartIIIb.Concrete.Wiring.ModeAux.StressLiftY
