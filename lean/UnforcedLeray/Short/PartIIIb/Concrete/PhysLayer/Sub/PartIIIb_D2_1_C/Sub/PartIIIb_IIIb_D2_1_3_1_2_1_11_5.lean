import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_11
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_11_1
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_11_2
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_11_3
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.TruncMemY
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_1_C.AdjTruncOrg.CutBounds

/-!
# `laplPair`: `νΔΦₙ = lapA n ν D aΦ` weakly

Source `the November 2 reference manuscript` lines 1334-1337, 1351-1362, 1470-1480.
`truncPhi = χ Φ + ∑ᵢ ∂ᵢχ (eᵢ × ψ)` and `lapA = χ aΦ + 2ν ∑ₖ ∂ₖχ ∂ₖΦ + νΔχ Φ + lapCross`.
Each piece is a weak product rule (`weakLapMul`) applied to `Φ` and to `eᵢ × ψ`, with
`weakLapLin` for the cross products and `weakLapPsi` for `Δψ`; the pieces are paired against
phase tests with the integrability supplied by `LocL2`. Helpers are local (prefix `lpc_`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-! ### Cross product and gradient algebra -/

theorem lpc_add_left (a b v : CVec3) : crossC (a + b) v = crossC a v + crossC b v := by
  ext i; fin_cases i <;> simp [crossC] <;> ring

theorem lpc_smul_left (r : ℝ) (a v : CVec3) : crossC (r • a) v = r • crossC a v := by
  ext i; fin_cases i <;> simp [crossC, Complex.real_smul] <;> ring

theorem lpc_add_right (a b v : CVec3) : crossC a (b + v) = crossC a b + crossC a v := by
  ext i; fin_cases i <;> simp [crossC] <;> ring

theorem lpc_smul_right (r : ℝ) (a v : CVec3) : crossC a (r • v) = r • crossC a v := by
  ext i; fin_cases i <;> simp [crossC, Complex.real_smul] <;> ring

theorem lpc_neg_right (a v : CVec3) : crossC a (-v) = -crossC a v := by
  ext i; fin_cases i <;> simp [crossC] <;> ring

theorem lpc_gradC_eq (a : Space → ℝ) (y : Space) :
    gradC a y = ∑ i : Fin 3, sd i a y • EuclideanSpace.single i (1 : ℂ) := by
  ext j
  fin_cases j <;> simp [gradC, Fin.sum_univ_three, Complex.real_smul]

theorem lpc_crossC_gradC (a : Space → ℝ) (y : Space) (v : CVec3) :
    crossC (gradC a y) v = ∑ i : Fin 3, sd i a y • crossC (EuclideanSpace.single i (1 : ℂ)) v := by
  rw [lpc_gradC_eq]
  simp only [Fin.sum_univ_three, lpc_add_left, lpc_smul_left]

theorem lpc_abs_sd_le (f : Space → ℝ) (y : Space) (i : Fin 3) : |sd i f y| ≤ ‖gradC f y‖ := by
  have h : ‖gradC f y i‖ ≤ ‖gradC f y‖ := PiLp.norm_apply_le (gradC f y) i
  have e : gradC f y i = ((sd i f y : ℝ) : ℂ) := rfl
  rw [e, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

/-! ### Derivatives of scalar functions -/

theorem lpc_sd_comm {a : Space → ℝ} (ha : ContDiff ℝ ∞ a) (i k : Fin 3) :
    sd i (sd k a) = sd k (sd i a) := by
  funext y
  have hd : Differentiable ℝ (fderiv ℝ a) :=
    (ha.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have h1 : ∀ w v : Space, fderiv ℝ (fun p => fderiv ℝ a p w) y v =
      fderiv ℝ (fderiv ℝ a) y v w := by
    intro w v
    have hx : HasFDerivAt (fun p => fderiv ℝ a p w) ((fderiv ℝ (fderiv ℝ a) y).flip w) y := by
      simpa using (hd y).hasFDerivAt.clm_apply (hasFDerivAt_const w y)
    rw [hx.fderiv]
    rfl
  have hs := (ha.contDiffAt (x := y)).isSymmSndFDerivAt (by simp)
  show fderiv ℝ (fun p => fderiv ℝ a p (coordinateVector k)) y (coordinateVector i) =
    fderiv ℝ (fun p => fderiv ℝ a p (coordinateVector i)) y (coordinateVector k)
  rw [h1, h1]
  exact hs.eq _ _

theorem lpc_contDiff_lapS {a : Space → ℝ} (ha : ContDiff ℝ ∞ a) : ContDiff ℝ ∞ (lapS a) := by
  unfold lapS
  exact ContDiff.sum fun j _ =>
    UnforcedLeray.PhaseSpace.contDiff_sd (UnforcedLeray.PhaseSpace.contDiff_sd ha j) j

theorem lpc_sd_lapS {a : Space → ℝ} (ha : ContDiff ℝ ∞ a) (i : Fin 3) :
    sd i (lapS a) = lapS (sd i a) := by
  funext y
  have hd : ∀ j : Fin 3, DifferentiableAt ℝ (fun z => sd j (sd j a) z) y := fun j =>
    ((UnforcedLeray.PhaseSpace.contDiff_sd
      (UnforcedLeray.PhaseSpace.contDiff_sd ha j) j).differentiable (by simp)) y
  show fderiv ℝ (fun z => ∑ j : Fin 3, sd j (sd j a) z) y (coordinateVector i) =
    ∑ j : Fin 3, sd j (sd j (sd i a)) y
  rw [fderiv_fun_sum (fun j _ => hd j)]
  simp only [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  show sd i (sd j (sd j a)) y = sd j (sd j (sd i a)) y
  rw [lpc_sd_comm (UnforcedLeray.PhaseSpace.contDiff_sd ha j) i j, lpc_sd_comm ha i j]

/-! ### Integrability in `Y_2` -/

theorem lpc_sum3 {P : ℝ} (hP : 0 < P) {f0 f1 f2 : ℝ × Space → CVec3}
    (h0 : UnforcedLeray.Short.IIb.IsInYr P 2 f0) (h1 : UnforcedLeray.Short.IIb.IsInYr P 2 f1)
    (h2 : UnforcedLeray.Short.IIb.IsInYr P 2 f2) :
    UnforcedLeray.Short.IIb.IsInYr P 2 (fun x => f0 x + f1 x + f2 x) :=
  isInYr_add2 hP (F := fun x => f0 x + f1 x + f2 x) (fun _ => rfl)
    (isInYr_add2 hP (F := fun x => f0 x + f1 x) (fun _ => rfl) h0 h1) h2

theorem lpc_isInYr_sum3_fin {P : ℝ} (hP : 0 < P) {g : Fin 3 → ℝ × Space → CVec3}
    (h : ∀ k, UnforcedLeray.Short.IIb.IsInYr P 2 (g k)) :
    UnforcedLeray.Short.IIb.IsInYr P 2 (fun x => ∑ k : Fin 3, g k x) := by
  have e : (fun x => ∑ k : Fin 3, g k x) = fun x => g 0 x + g 1 x + g 2 x :=
    funext fun x => Fin.sum_univ_three _
  rw [e]
  exact lpc_sum3 hP (h 0) (h 1) (h 2)

theorem lpc_isInYr_bdd_smul {P : ℝ} (hP : 0 < P) {f : Space → ℝ} (hf : Continuous f) {M : ℝ}
    (hM : ∀ y, |f y| ≤ M) {g : ℝ × Space → CVec3}
    (hg : UnforcedLeray.Short.IIb.IsInYr P 2 g) :
    UnforcedLeray.Short.IIb.IsInYr P 2 (fun x => f x.2 • g x) :=
  isInYr_smul_of_bdd hP (a := fun x : ℝ × Space => f x.2) (M := M)
    (hf.comp continuous_snd).aestronglyMeasurable (fun x => hM x.2)
    (Filter.Eventually.of_forall fun _ => rfl) hg

theorem lpc_isInYr_const_smul {P : ℝ} (hP : 0 < P) (c : ℝ) {g : ℝ × Space → CVec3}
    (hg : UnforcedLeray.Short.IIb.IsInYr P 2 g) :
    UnforcedLeray.Short.IIb.IsInYr P 2 (fun x => c • g x) :=
  isInYr_smul_of_bdd hP (a := fun _ : ℝ × Space => c) (M := |c|)
    aestronglyMeasurable_const (fun _ => le_refl _) (Filter.Eventually.of_forall fun _ => rfl) hg

theorem lpc_isInYr_cross_const {P : ℝ} (hP : 0 < P) (e : CVec3) {g : ℝ × Space → CVec3}
    (hg : UnforcedLeray.Short.IIb.IsInYr P 2 g) :
    UnforcedLeray.Short.IIb.IsInYr P 2 (fun x => crossC e (g x)) :=
  isInYr_cross_bdd hP (A := fun _ : Space => e) (M := ‖e‖) (norm_nonneg e) (fun _ => le_rfl)
    continuous_const hg

/-- Local `L²` pieces (`Y_2` or the Hardy quotient in `Y_2`), closed under bounded scalar
multiplication and constant cross products. -/
theorem lpc_locL2_smul {P : ℝ} (hP : 0 < P) {g : Space → ℝ} (hg : Continuous g) {M : ℝ}
    (hM : ∀ y, |g y| ≤ M) {u : ℝ × Space → CVec3} (hu : LocL2 P u) :
    LocL2 P (fun x => g x.2 • u x) := by
  rcases hu with hY | hH
  · exact Or.inl (lpc_isInYr_bdd_smul hP hg hM hY)
  · refine Or.inr ?_
    have h := lpc_isInYr_bdd_smul hP hg hM hH
    have e : (fun x : ℝ × Space => (‖x.2‖⁻¹ : ℝ) • (g x.2 • u x)) =
        fun x => g x.2 • ((‖x.2‖⁻¹ : ℝ) • u x) := by
      funext x
      rw [smul_smul, smul_smul, mul_comm]
    show UnforcedLeray.Short.IIb.IsInYr P 2 (fun x : ℝ × Space => (‖x.2‖⁻¹ : ℝ) • (g x.2 • u x))
    rw [e]
    exact h

theorem lpc_locL2_cross {P : ℝ} (hP : 0 < P) (e : CVec3) {u : ℝ × Space → CVec3}
    (hu : LocL2 P u) : LocL2 P (fun x => crossC e (u x)) := by
  rcases hu with hY | hH
  · exact Or.inl (lpc_isInYr_cross_const hP e hY)
  · refine Or.inr ?_
    have h := lpc_isInYr_cross_const hP e hH
    have e' : (fun x : ℝ × Space => (‖x.2‖⁻¹ : ℝ) • crossC e (u x)) =
        fun x => crossC e ((‖x.2‖⁻¹ : ℝ) • u x) := by
      funext x
      rw [lpc_smul_right]
    show UnforcedLeray.Short.IIb.IsInYr P 2 (fun x : ℝ × Space => (‖x.2‖⁻¹ : ℝ) • crossC e (u x))
    rw [e']
    exact h

/-- The right side `-ν ∑ₖ eₖ × ∂ₖΦ` of `WeakLapPsi`. -/
def lpcPsiA (ν : ℝ) (DΦ : Fin 3 → ℝ × Space → CVec3) : ℝ × Space → CVec3 :=
  fun x => -ν • ∑ k : Fin 3, crossC (EuclideanSpace.single k (1 : ℂ)) (DΦ k x)

theorem lpc_isInYr_aPsi {P : ℝ} (hP : 0 < P) (ν : ℝ) (DΦ : Fin 3 → ℝ × Space → CVec3)
    (hD : ∀ k, UnforcedLeray.Short.IIb.IsInYr P 2 (DΦ k)) :
    UnforcedLeray.Short.IIb.IsInYr P 2 (lpcPsiA ν DΦ) := by
  have hs := lpc_isInYr_sum3_fin hP (g := fun k x => crossC (EuclideanSpace.single k (1 : ℂ)) (DΦ k x))
    (fun k => lpc_isInYr_cross_const hP _ (hD k))
  exact lpc_isInYr_const_smul hP (-ν) hs

/-! ### Pairing decomposition -/

theorem lpc_pair3 {P : ℝ} (hP : 0 < P) {X f0 f1 f2 : ℝ × Space → CVec3} (hX : IsPhaseTest P X)
    (h0 : LocL2 P f0) (h1 : LocL2 P f1) (h2 : LocL2 P f2) :
    Integrable (fun z => dotL (X z) (f0 z + f1 z + f2 z)) (muP P) ∧
      pairF P X (fun x => f0 x + f1 x + f2 x) = pairF P X f0 + pairF P X f1 + pairF P X f2 := by
  have i0 := wlq_integrable hP hX h0
  have i1 := wlq_integrable hP hX h1
  have i2 := wlq_integrable hP hX h2
  have i01 := wlq_integrable_add_right i0 i1
  refine ⟨wlq_integrable_add_right i01 i2, ?_⟩
  calc pairF P X (fun x => f0 x + f1 x + f2 x)
      = pairF P X (fun x => f0 x + f1 x) + pairF P X f2 := wlq_pairF_add_right i01 i2
    _ = pairF P X f0 + pairF P X f1 + pairF P X f2 := by rw [wlq_pairF_add_right i0 i1]

/-! ### Cross derivative: `∂ₖ` against `eᵢ × ψ` -/

theorem lpc_cross_grad {P ν μ : ℝ} {D : TruncData} (hD : TruncHyp P ν μ D) (k : Fin 3)
    (e : CVec3) :
    UnforcedLeray.Short.IIb.HasPtwOp P (fun Θ => -dy k Θ) (fun x => crossC e (D.ψ x))
      (fun x => crossC e (D.Dψ k x)) := by
  intro Θ hΘ
  show pairF P (-dy k Θ) (fun x => crossC e (D.ψ x)) =
    pairF P Θ (fun x => crossC e (D.Dψ k x))
  have hΞ : IsPhaseTest P (fun x => crossC e (Θ x)) := wlq_phase_cross e hΘ
  have hdy : dy k (fun x => crossC e (Θ x)) = fun x => crossC e (dy k Θ x) :=
    wlq_dy_clm (L := wlqL e) (hΘ.smooth.differentiable (by simp)) k
  have hstep : pairF P (-dy k (fun x => crossC e (Θ x))) D.ψ
      = pairF P (fun x => crossC e (Θ x)) (D.Dψ k) := (hD.spΦ.grad k).2 _ hΞ
  have hneg : (fun x => crossC e ((-dy k Θ) x)) = -dy k (fun x => crossC e (Θ x)) := by
    rw [hdy]
    funext x
    simp only [Pi.neg_apply]
    exact lpc_neg_right e _
  rw [wlq_pairF_cross_right P e (-dy k Θ) D.ψ, wlq_pairF_cross_right P e Θ (D.Dψ k), hneg,
    hstep]

/-! ### Pieces of the weak identity -/

def lpcV0 (n : ℕ) (D : TruncData) : ℝ × Space → CVec3 := fun x => cutχ n x.2 • D.Φ x

def lpcW (n : ℕ) (D : TruncData) (i : Fin 3) : ℝ × Space → CVec3 :=
  fun x => sd i (cutχ n) x.2 • crossC (EuclideanSpace.single i (1 : ℂ)) (D.ψ x)

def lpcO0 (n : ℕ) (ν : ℝ) (D : TruncData) (aΦ : ℝ × Space → CVec3) : ℝ × Space → CVec3 :=
  fun x => cutχ n x.2 • aΦ x + (2 * ν) • ∑ k : Fin 3, sd k (cutχ n) x.2 • D.DΦ k x
    + (ν * lapS (cutχ n) x.2) • D.Φ x

def lpcY (n : ℕ) (ν : ℝ) (D : TruncData) (i : Fin 3) : ℝ × Space → CVec3 :=
  fun x => sd i (cutχ n) x.2 • crossC (EuclideanSpace.single i (1 : ℂ)) (lpcPsiA ν D.DΦ x)
    + (2 * ν) • ∑ k : Fin 3, sd k (sd i (cutχ n)) x.2 •
        crossC (EuclideanSpace.single i (1 : ℂ)) (D.Dψ k x)

def lpcH (n : ℕ) (ν : ℝ) (D : TruncData) (i : Fin 3) : ℝ × Space → CVec3 :=
  fun x => (ν * lapS (sd i (cutχ n)) x.2) • crossC (EuclideanSpace.single i (1 : ℂ)) (D.ψ x)

/-- **laplPair** (source 1334-1337, 1351-1362, 1470-1480): `νΔΦₙ = lapA` weakly. -/
theorem laplPair : LaplPair := by
  intro P ν μ hP hP1 hν hμ D hD n aΦ haΦ hpair
  have hcb := cutBounds
  unfold CutBounds at hcb
  obtain ⟨C, hC0, hb⟩ := hcb
  have hcut : ContDiff ℝ ∞ (cutχ n) := UnforcedLeray.PhaseSpace.contDiff_cutχ n
  have hsd : ∀ i : Fin 3, ContDiff ℝ ∞ (sd i (cutχ n)) := fun i =>
    UnforcedLeray.PhaseSpace.contDiff_sd hcut i
  have hlap : ContDiff ℝ ∞ (lapS (cutχ n)) := lpc_contDiff_lapS hcut
  have hdivC : C / ((n : ℝ) + 1) ≤ C := div_le_self hC0 (by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith)
  have hbK : ∀ (i : Fin 3) (y : Space), |sd i (cutχ n) y| ≤ C :=
    fun i y => ((hb n y).2.2.2.2.2.2 i).1
  have hbL : ∀ y : Space, |lapS (cutχ n) y| ≤ C := fun y => (hb n y).2.2.2.2.2.1
  have hbT : ∀ (i k : Fin 3) (y : Space), |sd k (sd i (cutχ n)) y| ≤ C := by
    intro i k y
    rw [lpc_sd_comm hcut k i]
    exact (lpc_abs_sd_le (sd k (cutχ n)) y i).trans ((hb n y).2.2.2.2.2.2 k).2
  have hbLS : ∀ (i : Fin 3) (y : Space), |lapS (sd i (cutχ n)) y| ≤ C := by
    intro i y
    rw [← lpc_sd_lapS hcut i]
    exact (lpc_abs_sd_le (lapS (cutχ n)) y i).trans ((hb n y).2.2.2.1.trans hdivC)
  have hcb1 : ∀ y : Space, |cutχ n y| ≤ 1 := fun y => by
    have h0 : (0 : ℝ) ≤ unitBump (cutC n • y) := unitBump.nonneg
    have h1 : unitBump (cutC n • y) ≤ 1 := unitBump.le_one
    unfold cutχ
    exact abs_le.2 ⟨by linarith, h1⟩
  have hcontKK : ∀ i k : Fin 3, Continuous (sd k (sd i (cutχ n))) := fun i k =>
    (UnforcedLeray.PhaseSpace.contDiff_sd (hsd i) k).continuous
  have hcontLS : ∀ i : Fin 3, Continuous (lapS (sd i (cutχ n))) := fun i =>
    (lpc_contDiff_lapS (hsd i)).continuous
  have hΦ : UnforcedLeray.Short.IIb.IsInYr P 2 D.Φ := hD.dom.mem
  have hDΦ : ∀ k : Fin 3, UnforcedLeray.Short.IIb.IsInYr P 2 (D.DΦ k) := fun k => (hD.dΦ k).1
  have hDψ : ∀ k : Fin 3, UnforcedLeray.Short.IIb.IsInYr P 2 (D.Dψ k) :=
    fun k => (hD.spΦ.grad k).1
  have hLψ : LocL2 P D.ψ := Or.inr hD.spΦ.hardy
  have hLΦ : LocL2 P D.Φ := Or.inl hΦ
  have hAψ : UnforcedLeray.Short.IIb.IsInYr P 2 (lpcPsiA ν D.DΦ) :=
    lpc_isInYr_aPsi hP ν D.DΦ hDΦ
  have hψA : UnforcedLeray.Short.IIb.HasPtwOp P (nuLapT ν) D.ψ (lpcPsiA ν D.DΦ) :=
    weakLapPsi P ν μ D hD
  -- the `χ Φ` piece and its weak product rule
  have hA0 : UnforcedLeray.Short.IIb.HasPtwOp P (nuLapT ν) (lpcV0 n D) (lpcO0 n ν D aΦ) :=
    weakLapMul P ν hP (cutχ n) hcut D.Φ aΦ D.DΦ hLΦ (Or.inl haΦ) (fun k => Or.inl (hDΦ k))
      hpair (fun k => (hD.dΦ k).2)
  -- the `eᵢ × ψ` pieces and their weak product rules
  have hPi : ∀ i : Fin 3, UnforcedLeray.Short.IIb.HasPtwOp P (nuLapT ν)
      (fun x => crossC (EuclideanSpace.single i (1 : ℂ)) (D.ψ x))
      (fun x => crossC (EuclideanSpace.single i (1 : ℂ)) (lpcPsiA ν D.DΦ x)) := fun i =>
    (weakLapLin P ν hP D.ψ D.ψ (lpcPsiA ν D.DΦ) (lpcPsiA ν D.DΦ) hLψ hLψ (Or.inl hAψ)
      (Or.inl hAψ) hψA hψA).2.2 _
  have hAi : ∀ i : Fin 3, UnforcedLeray.Short.IIb.HasPtwOp P (nuLapT ν) (lpcW n D i)
      (fun x => lpcY n ν D i x + lpcH n ν D i x) := fun i =>
    weakLapMul P ν hP (sd i (cutχ n)) (hsd i)
      (fun x => crossC (EuclideanSpace.single i (1 : ℂ)) (D.ψ x))
      (fun x => crossC (EuclideanSpace.single i (1 : ℂ)) (lpcPsiA ν D.DΦ x))
      (fun k x => crossC (EuclideanSpace.single i (1 : ℂ)) (D.Dψ k x))
      (lpc_locL2_cross hP _ hLψ) (lpc_locL2_cross hP _ (Or.inl hAψ))
      (fun k => lpc_locL2_cross hP _ (Or.inl (hDψ k)))
      (hPi i) (fun k => lpc_cross_grad hD k _)
  -- local `L²` of the pieces
  have hV0 : LocL2 P (lpcV0 n D) :=
    Or.inl (lpc_isInYr_bdd_smul hP hcut.continuous hcb1 hΦ)
  have hW : ∀ i : Fin 3, LocL2 P (lpcW n D i) := fun i =>
    lpc_locL2_smul hP (hsd i).continuous (hbK i)
      (lpc_locL2_cross hP (EuclideanSpace.single i (1 : ℂ)) hLψ)
  have hH : ∀ i : Fin 3, LocL2 P (lpcH n ν D i) := fun i =>
    lpc_locL2_smul hP (g := fun y => ν * lapS (sd i (cutχ n)) y)
      (continuous_const.mul (hcontLS i)) (M := |ν| * C)
      (fun y => by
        show |ν * lapS (sd i (cutχ n)) y| ≤ |ν| * C
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hbLS i y) (abs_nonneg ν))
      (lpc_locL2_cross hP (EuclideanSpace.single i (1 : ℂ)) hLψ)
  have hY : ∀ i : Fin 3, LocL2 P (lpcY n ν D i) := fun i => by
    have hA := lpc_isInYr_bdd_smul hP (hsd i).continuous (hbK i)
      (lpc_isInYr_cross_const hP (EuclideanSpace.single i (1 : ℂ)) hAψ)
    have hB := lpc_isInYr_const_smul hP (2 * ν)
      (lpc_isInYr_sum3_fin hP (g := fun k x => sd k (sd i (cutχ n)) x.2 •
          crossC (EuclideanSpace.single i (1 : ℂ)) (D.Dψ k x))
        (fun k => lpc_isInYr_bdd_smul hP (hcontKK i k) (hbT i k)
          (lpc_isInYr_cross_const hP (EuclideanSpace.single i (1 : ℂ)) (hDψ k))))
    exact Or.inl (isInYr_add2 hP (F := lpcY n ν D i) (fun _ => rfl) hA hB)
  -- `O₀ = χ aΦ + 2ν ∑ₖ ∂ₖχ ∂ₖΦ + νΔχ Φ` is in `Y_2`
  have hO0Y : UnforcedLeray.Short.IIb.IsInYr P 2 (lpcO0 n ν D aΦ) := by
    have T1 := lpc_isInYr_bdd_smul hP hcut.continuous hcb1 haΦ
    have T2 := lpc_isInYr_const_smul hP (2 * ν)
      (lpc_isInYr_sum3_fin hP (g := fun k x => sd k (cutχ n) x.2 • D.DΦ k x)
        (fun k => lpc_isInYr_bdd_smul hP (hsd k).continuous (hbK k) (hDΦ k)))
    have T3 := lpc_isInYr_bdd_smul hP (f := fun y => ν * lapS (cutχ n) y)
      (continuous_const.mul hlap.continuous) (M := |ν| * C)
      (fun y => by
        show |ν * lapS (cutχ n) y| ≤ |ν| * C
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hbL y) (abs_nonneg ν)) hΦ
    exact lpc_sum3 hP T1 T2 T3
  have hO0 : LocL2 P (lpcO0 n ν D aΦ) := Or.inl hO0Y
  -- pointwise identities
  have hTP : truncPhi n D = fun x => lpcV0 n D x + (lpcW n D 0 x + lpcW n D 1 x + lpcW n D 2 x) := by
    funext x
    simp only [truncPhi, lpcV0, lpcW, lpc_crossC_gradC, Fin.sum_univ_three, add_assoc]
  have hAP : lapA n ν D aΦ = fun x => lpcO0 n ν D aΦ x
      + (lpcY n ν D 0 x + lpcY n ν D 1 x + lpcY n ν D 2 x)
      + (lpcH n ν D 0 x + lpcH n ν D 1 x + lpcH n ν D 2 x) := by
    funext x
    simp only [lapA, lapCross, lpcO0, lpcY, lpcH, lpcPsiA, Fin.sum_univ_three,
      lpc_crossC_gradC, lpc_add_right, lpc_smul_right, ← lpc_sd_lapS hcut, lpc_sd_comm hcut,
      add_assoc, smul_add]
    module
  rw [hTP, hAP]
  intro Θ hΘ
  have hX : IsPhaseTest P (nuLapT ν Θ) := hΘ.lapT.const_smul ν
  have hO0Θ := hA0 Θ hΘ
  have hWi : ∀ i : Fin 3, pairF P (nuLapT ν Θ) (lpcW n D i) =
      pairF P Θ (lpcY n ν D i) + pairF P Θ (lpcH n ν D i) := by
    intro i
    rw [hAi i Θ hΘ]
    exact wlq_pairF_add_right (wlq_integrable hP hΘ (hY i)) (wlq_integrable hP hΘ (hH i))
  have hLW := lpc_pair3 hP hX (hW 0) (hW 1) (hW 2)
  have hLV : pairF P (nuLapT ν Θ) (fun x => lpcV0 n D x + (lpcW n D 0 x + lpcW n D 1 x + lpcW n D 2 x))
      = pairF P (nuLapT ν Θ) (lpcV0 n D)
        + pairF P (nuLapT ν Θ) (fun x => lpcW n D 0 x + lpcW n D 1 x + lpcW n D 2 x) :=
    wlq_pairF_add_right (wlq_integrable hP hX hV0) hLW.1
  have iO := wlq_integrable hP hΘ hO0
  have iY := lpc_pair3 hP hΘ (hY 0) (hY 1) (hY 2)
  have iH := lpc_pair3 hP hΘ (hH 0) (hH 1) (hH 2)
  have iOY := wlq_integrable_add_right iO iY.1
  have hRHS : pairF P Θ (fun x => lpcO0 n ν D aΦ x
      + (lpcY n ν D 0 x + lpcY n ν D 1 x + lpcY n ν D 2 x)
      + (lpcH n ν D 0 x + lpcH n ν D 1 x + lpcH n ν D 2 x))
      = pairF P Θ (lpcO0 n ν D aΦ)
        + (pairF P Θ (lpcY n ν D 0) + pairF P Θ (lpcY n ν D 1) + pairF P Θ (lpcY n ν D 2))
        + (pairF P Θ (lpcH n ν D 0) + pairF P Θ (lpcH n ν D 1) + pairF P Θ (lpcH n ν D 2)) := by
    have e1 : pairF P Θ (fun x => lpcO0 n ν D aΦ x
        + (lpcY n ν D 0 x + lpcY n ν D 1 x + lpcY n ν D 2 x)
        + (lpcH n ν D 0 x + lpcH n ν D 1 x + lpcH n ν D 2 x))
        = pairF P Θ (fun x => lpcO0 n ν D aΦ x
          + (lpcY n ν D 0 x + lpcY n ν D 1 x + lpcY n ν D 2 x))
          + pairF P Θ (fun x => lpcH n ν D 0 x + lpcH n ν D 1 x + lpcH n ν D 2 x) :=
      wlq_pairF_add_right iOY iH.1
    have e2 : pairF P Θ (fun x => lpcO0 n ν D aΦ x
          + (lpcY n ν D 0 x + lpcY n ν D 1 x + lpcY n ν D 2 x))
        = pairF P Θ (lpcO0 n ν D aΦ)
          + pairF P Θ (fun x => lpcY n ν D 0 x + lpcY n ν D 1 x + lpcY n ν D 2 x) :=
      wlq_pairF_add_right iO iY.1
    rw [e1, e2, iY.2, iH.2]
  linear_combination hLV + hLW.2 + hO0Θ + hWi 0 + hWi 1 + hWi 2 - hRHS

end UnforcedLeray.Short.PartIIIb.Concrete
