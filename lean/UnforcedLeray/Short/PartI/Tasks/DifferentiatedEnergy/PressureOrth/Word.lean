import UnforcedLeray.Short.PartI.Sub.PartI_T08_6

/-!


Source: `the November 2 reference manuscript`, line 346.

For `w = β :: w'` the proof uses:
* `H = ∂_w P = ∂_β(∂_{w'} P)` is in `L²(cell)` (commutation of word derivatives with partials);
* `∂_k(∂_w f_k)` is the word derivative of `f_k` with one more letter, hence in `L²(cell)`;
* the periodic integration by parts `integral_cell_partialQ_mul` (`k = 0`) and
  `integral_cell_partialEta_mul` (`k = 1`), which move `∂_k` from `∂_w P` onto `∂_w f_k`;
* `∑_k ∂_k ∂_w f_k = ∂_w (div f) = 0` pointwise.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

namespace JetPressureWord

/-- Word derivatives commute with `∂_q` on smooth functions. -/
theorem derivWord_partialQ (w : List Bool) {g : Plane → ℝ} (hg : ContDiff ℝ ∞ g) :
    B0151.derivWord w (fun z => Cyl.partialQ g z) = fun z => Cyl.partialQ (B0151.derivWord w g) z := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    have hu : ContDiff ℝ ∞ (B0151.derivWord w g) := B0151.contDiff_derivWord hg w
    cases b with
    | false =>
      show Cyl.partialEta (B0151.derivWord w (fun z => Cyl.partialQ g z))
        = fun z => Cyl.partialQ (Cyl.partialEta (B0151.derivWord w g)) z
      rw [ih]
      exact (JetViscIBP.comm_QE hu).symm
    | true =>
      show Cyl.partialQ (B0151.derivWord w (fun z => Cyl.partialQ g z))
        = fun z => Cyl.partialQ (Cyl.partialQ (B0151.derivWord w g)) z
      rw [ih]

/-- Word derivatives commute with `∂_η` on smooth functions. -/
theorem derivWord_partialEta (w : List Bool) {g : Plane → ℝ} (hg : ContDiff ℝ ∞ g) :
    B0151.derivWord w (fun z => Cyl.partialEta g z) = fun z => Cyl.partialEta (B0151.derivWord w g) z := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    have hu : ContDiff ℝ ∞ (B0151.derivWord w g) := B0151.contDiff_derivWord hg w
    cases b with
    | false =>
      show Cyl.partialEta (B0151.derivWord w (fun z => Cyl.partialEta g z))
        = fun z => Cyl.partialEta (Cyl.partialEta (B0151.derivWord w g)) z
      rw [ih]
    | true =>
      show Cyl.partialQ (B0151.derivWord w (fun z => Cyl.partialEta g z))
        = fun z => Cyl.partialEta (Cyl.partialQ (B0151.derivWord w g)) z
      rw [ih]
      exact JetViscIBP.comm_QE hu

/-- Word derivatives are additive on smooth functions. -/
theorem derivWord_add (w : List Bool) {A B : Plane → ℝ} (hA : ContDiff ℝ ∞ A)
    (hB : ContDiff ℝ ∞ B) :
    B0151.derivWord w (fun z => A z + B z)
      = fun z => B0151.derivWord w A z + B0151.derivWord w B z := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    have hAw : Differentiable ℝ (B0151.derivWord w A) :=
      (B0151.contDiff_derivWord hA w).differentiable (by simp)
    have hBw : Differentiable ℝ (B0151.derivWord w B) :=
      (B0151.contDiff_derivWord hB w).differentiable (by simp)
    cases b with
    | false =>
      show Cyl.partialEta (B0151.derivWord w (fun z => A z + B z))
        = fun z => Cyl.partialEta (B0151.derivWord w A) z + Cyl.partialEta (B0151.derivWord w B) z
      rw [ih]
      funext z
      exact JetViscIBP.partialEta_add_pt hAw hBw z
    | true =>
      show Cyl.partialQ (B0151.derivWord w (fun z => A z + B z))
        = fun z => Cyl.partialQ (B0151.derivWord w A) z + Cyl.partialQ (B0151.derivWord w B) z
      rw [ih]
      funext z
      exact JetViscIBP.partialQ_add_pt hAw hBw z

/-- Word derivatives of the zero function vanish. -/
theorem derivWord_zero (w : List Bool) :
    B0151.derivWord w (fun _ : Plane => (0 : ℝ)) = fun _ => 0 := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases b with
    | false =>
      show Cyl.partialEta (B0151.derivWord w (fun _ : Plane => (0 : ℝ))) = fun _ => 0
      rw [ih]
      funext z
      simp [Cyl.partialEta]
    | true =>
      show Cyl.partialQ (B0151.derivWord w (fun _ : Plane => (0 : ℝ))) = fun _ => 0
      rw [ih]
      funext z
      simp [Cyl.partialQ]

theorem comp_contDiff {f : Plane → Train.Vec} (hsm : ContDiff ℝ ∞ f) (k : Fin 2) :
    ContDiff ℝ ∞ (fun x => f x k) :=
  (EuclideanSpace.proj k : Train.Vec →L[ℝ] ℝ).contDiff.comp hsm

/-- The divergence cancels pointwise after word derivatives. -/
theorem sum_partials_zero (w : List Bool) {f : Plane → Train.Vec} (hsm : ContDiff ℝ ∞ f)
    (hdiv : ∀ z : Plane, Cyl.divergence f z = 0) (z : Plane) :
    Cyl.partialQ (wordComp w f 0) z + Cyl.partialEta (wordComp w f 1) z = 0 := by
  unfold wordComp
  have h0 : ContDiff ℝ ∞ (fun x => f x 0) := comp_contDiff hsm 0
  have h1 : ContDiff ℝ ∞ (fun x => f x 1) := comp_contDiff hsm 1
  have hQ : ContDiff ℝ ∞ (fun x => Cyl.partialQ (fun y => f y 0) x) :=
    JetViscIBP.cd_partialQ h0
  have hE : ContDiff ℝ ∞ (fun x => Cyl.partialEta (fun y => f y 1) x) :=
    JetViscIBP.cd_partialEta h1
  have cQ := derivWord_partialQ w h0
  have cE := derivWord_partialEta w h1
  have ad := derivWord_add w hQ hE
  have e1 : Cyl.partialQ (B0151.derivWord w (fun x => f x 0)) z
      = B0151.derivWord w (fun x => Cyl.partialQ (fun y => f y 0) x) z :=
    (congrFun cQ z).symm
  have e2 : Cyl.partialEta (B0151.derivWord w (fun x => f x 1)) z
      = B0151.derivWord w (fun x => Cyl.partialEta (fun y => f y 1) x) z :=
    (congrFun cE z).symm
  have e3 : B0151.derivWord w (fun x => Cyl.partialQ (fun y => f y 0) x
        + Cyl.partialEta (fun y => f y 1) x) z
      = B0151.derivWord w (fun x => Cyl.partialQ (fun y => f y 0) x) z
        + B0151.derivWord w (fun x => Cyl.partialEta (fun y => f y 1) x) z :=
    congrFun ad z
  have hfun : (fun x => Cyl.partialQ (fun y => f y 0) x + Cyl.partialEta (fun y => f y 1) x)
      = fun _ => (0 : ℝ) :=
    funext fun x => hdiv x
  have e4 : B0151.derivWord w (fun x => Cyl.partialQ (fun y => f y 0) x
        + Cyl.partialEta (fun y => f y 1) x) z = 0 := by
    rw [hfun]
    exact congrFun (derivWord_zero w) z
  rw [e1, e2]
  linarith [e3, e4]

end JetPressureWord

open JetPressureWord

theorem jetPressureOrthWord_proof : UnforcedLeray.Short.PartI.JetPressureOrthWord := by
  intro c hc f hf hdiv P hP hper hL2P w hw
  obtain ⟨hsm, hper_f, hL2⟩ := hf
  have hWs : ∀ (v : List Bool) (k : Fin 2), ContDiff ℝ ∞ (wordComp v f k) := fun v k =>
    B0151.contDiff_derivWord (comp_contDiff hsm k) v
  have hWp : ∀ (v : List Bool) (k : Fin 2), Cyl.IsPeriodic c (wordComp v f k) := by
    intro v k
    refine JetViscIBP.per_derivWord v (fun x => f x k) ?_
    intro z
    show f (z.1 + c, z.2) k = f z k
    rw [hper_f z]
  obtain ⟨β, w', rfl⟩ : ∃ β w', w = β :: w' := by
    cases w with
    | nil => exact absurd rfl hw
    | cons b u => exact ⟨b, u, rfl⟩
  have hH : ContDiff ℝ ∞ (B0151.derivWord (β :: w') P) := B0151.contDiff_derivWord hP _
  have dH : Differentiable ℝ (B0151.derivWord (β :: w') P) := hH.differentiable (by simp)
  have hHper : Cyl.IsPeriodic c (B0151.derivWord (β :: w') P) :=
    JetViscIBP.per_derivWord (β :: w') P hper
  -- `∂_k (∂_w P)` is the word derivative `∂_w ∂_k P`
  have g0 : wordComp (β :: w') (Train.gradS P) 0
      = fun z => Cyl.partialQ (B0151.derivWord (β :: w') P) z :=
    derivWord_partialQ (β :: w') hP
  have g1 : wordComp (β :: w') (Train.gradS P) 1
      = fun z => Cyl.partialEta (B0151.derivWord (β :: w') P) z :=
    derivWord_partialEta (β :: w') hP
  -- `∂_w P` is in `L²(cell)`
  have hHL2 : MemLp (B0151.derivWord (β :: w') P) 2 (Cyl.cellμ c) := by
    cases β with
    | true =>
      have e : B0151.derivWord (true :: w') P = wordComp w' (Train.gradS P) 0 :=
        (derivWord_partialQ w' hP).symm
      rw [e]
      exact hL2P w' 0
    | false =>
      have e : B0151.derivWord (false :: w') P = wordComp w' (Train.gradS P) 1 :=
        (derivWord_partialEta w' hP).symm
      rw [e]
      exact hL2P w' 1
  have hQH : MemLp (fun z => Cyl.partialQ (B0151.derivWord (β :: w') P) z) 2 (Cyl.cellμ c) := by
    have := hL2P (β :: w') 0
    rw [g0] at this
    exact this
  have hEH : MemLp (fun z => Cyl.partialEta (B0151.derivWord (β :: w') P) z) 2 (Cyl.cellμ c) := by
    have := hL2P (β :: w') 1
    rw [g1] at this
    exact this
  -- the `k = 0` integration by parts (in `q`)
  have I0 : ∫ z in Cyl.cell c, wordComp (β :: w') f 0 z * wordComp (β :: w') (Train.gradS P) 0 z
      = -∫ z in Cyl.cell c, B0151.derivWord (β :: w') P z * Cyl.partialQ (wordComp (β :: w') f 0) z := by
    have e : ∀ z, wordComp (β :: w') f 0 z * wordComp (β :: w') (Train.gradS P) 0 z
        = Cyl.partialQ (B0151.derivWord (β :: w') P) z * wordComp (β :: w') f 0 z := by
      intro z
      have hz : wordComp (β :: w') (Train.gradS P) 0 z
          = Cyl.partialQ (B0151.derivWord (β :: w') P) z := congrFun g0 z
      rw [hz]
      ring
    simp only [e]
    have h1 : IntegrableOn (fun z => Cyl.partialQ (B0151.derivWord (β :: w') P) z
        * wordComp (β :: w') f 0 z) (Cyl.cell c) :=
      hQH.integrable_mul (hL2 (β :: w') 0)
    have h2 : IntegrableOn (fun z => B0151.derivWord (β :: w') P z
        * Cyl.partialQ (wordComp (β :: w') f 0) z) (Cyl.cell c) :=
      (hHL2.integrable_mul (hL2 (true :: (β :: w')) 0))
    exact Cyl.integral_cell_partialQ_mul hc dH
      (((B0151.contDiff_derivWord (comp_contDiff hsm 0) (β :: w'))).differentiable (by simp))
      hHper (hWp (β :: w') 0) h1 h2
  -- the `k = 1` integration by parts (in `η`)
  have I1 : ∫ z in Cyl.cell c, wordComp (β :: w') f 1 z * wordComp (β :: w') (Train.gradS P) 1 z
      = -∫ z in Cyl.cell c, B0151.derivWord (β :: w') P z * Cyl.partialEta (wordComp (β :: w') f 1) z := by
    have e : ∀ z, wordComp (β :: w') f 1 z * wordComp (β :: w') (Train.gradS P) 1 z
        = Cyl.partialEta (B0151.derivWord (β :: w') P) z * wordComp (β :: w') f 1 z := by
      intro z
      have hz : wordComp (β :: w') (Train.gradS P) 1 z
          = Cyl.partialEta (B0151.derivWord (β :: w') P) z := congrFun g1 z
      rw [hz]
      ring
    simp only [e]
    have h0 : IntegrableOn (fun z => B0151.derivWord (β :: w') P z * wordComp (β :: w') f 1 z)
        (Cyl.cell c) :=
      hHL2.integrable_mul (hL2 (β :: w') 1)
    have h1 : IntegrableOn (fun z => Cyl.partialEta (B0151.derivWord (β :: w') P) z
        * wordComp (β :: w') f 1 z) (Cyl.cell c) :=
      hEH.integrable_mul (hL2 (β :: w') 1)
    have h2 : IntegrableOn (fun z => B0151.derivWord (β :: w') P z
        * Cyl.partialEta (wordComp (β :: w') f 1) z) (Cyl.cell c) :=
      hHL2.integrable_mul (hL2 (false :: (β :: w')) 1)
    exact Cyl.integral_cell_partialEta_mul dH
      ((B0151.contDiff_derivWord (comp_contDiff hsm 1) (β :: w')).differentiable (by simp))
      h0 h1 h2
  -- the two boundary integrals cancel by the divergence condition
  have hI2 : IntegrableOn (fun z => B0151.derivWord (β :: w') P z
        * Cyl.partialQ (wordComp (β :: w') f 0) z) (Cyl.cell c) :=
    hHL2.integrable_mul (hL2 (true :: (β :: w')) 0)
  have hI3 : IntegrableOn (fun z => B0151.derivWord (β :: w') P z
        * Cyl.partialEta (wordComp (β :: w') f 1) z) (Cyl.cell c) :=
    hHL2.integrable_mul (hL2 (false :: (β :: w')) 1)
  have hsum : (∫ z in Cyl.cell c, B0151.derivWord (β :: w') P z * Cyl.partialQ (wordComp (β :: w') f 0) z)
      + (∫ z in Cyl.cell c, B0151.derivWord (β :: w') P z * Cyl.partialEta (wordComp (β :: w') f 1) z)
      = 0 := by
    rw [← integral_add hI2 hI3]
    have hz : ∀ z : Plane, B0151.derivWord (β :: w') P z * Cyl.partialQ (wordComp (β :: w') f 0) z
        + B0151.derivWord (β :: w') P z * Cyl.partialEta (wordComp (β :: w') f 1) z = 0 := by
      intro z
      rw [← mul_add, sum_partials_zero (β :: w') hsm hdiv z, mul_zero]
    simp only [hz, integral_zero]
  rw [Fin.sum_univ_two, I0, I1]
  linarith [hsum]

end UnforcedLeray.Short.PartI
