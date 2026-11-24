import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1_1
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ViscousIBP

/-!
# Part I, task `PartI:T08/4/1/1/3` (`TrainLapLocal`): proof

Source `the November 2 reference manuscript` lines 326-329.

`ν Δe` is smooth for `r > 0`, and a word derivative of `Δe` is a sum of two word derivatives of
`e` of order two higher (`JetViscIBP.derivWord_lap`, `derivWord` linear on smooth fields). The
local `L²` bound follows from `TrainErrJetLocalL2` applied to the two words `true::true::w` and
`false::false::w`, via `(a+b)² ≤ 2(a²+b²)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec Vc pc Qc width)

/-- Constant factors pass through word derivatives. -/
theorem lapLocal_dw_const_mul (c : ℝ) :
    ∀ (w : List Bool) (f : Plane → ℝ) (z : Plane),
      B0151.derivWord w (fun x => c * f x) z = c * B0151.derivWord w f z
  | [], f, z => rfl
  | true :: w, f, z => by
      have e : B0151.derivWord w (fun x => c * f x) = fun x => c * B0151.derivWord w f x :=
        funext (lapLocal_dw_const_mul c w f)
      show GaussianVortex.partialX (B0151.derivWord w (fun x => c * f x)) z =
        c * GaussianVortex.partialX (B0151.derivWord w f) z
      rw [e]
      unfold GaussianVortex.partialX
      rw [deriv_const_mul_field']
  | false :: w, f, z => by
      have e : B0151.derivWord w (fun x => c * f x) = fun x => c * B0151.derivWord w f x :=
        funext (lapLocal_dw_const_mul c w f)
      show GaussianVortex.partialY (B0151.derivWord w (fun x => c * f x)) z =
        c * GaussianVortex.partialY (B0151.derivWord w f) z
      rw [e]
      unfold GaussianVortex.partialY
      rw [deriv_const_mul_field']

/-- The scalar Laplacian of a smooth field is smooth. -/
theorem lapLocal_lapS_contDiff {g : Plane → ℝ} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun z => Train.lapS g z) :=
  (JetViscIBP.cd_partialQ (JetViscIBP.cd_partialQ hg)).add
    (JetViscIBP.cd_partialEta (JetViscIBP.cd_partialEta hg))

/-- A component of the vector Laplacian is the scalar Laplacian of the component. -/
theorem lapLocal_vecLap_apply (u : Plane → Vec) (z : Plane) (k : Fin 2) :
    Train.vecLaplacian u z k = Train.lapS (fun w => u w k) z := by
  fin_cases k <;> rfl

/-- Two-letter word derivatives of `g` add up to the scalar Laplacian of a word derivative. -/
theorem lapLocal_lapS_dw (w : List Bool) (g : Plane → ℝ) (z : Plane) :
    Train.lapS (B0151.derivWord w g) z =
      B0151.derivWord (true :: true :: w) g z + B0151.derivWord (false :: false :: w) g z := rfl

/-- The `L²` bound for a combination `ν (A + B)` from bounds on `A` and `B`. -/
theorem lapLocal_l2_comb (c ν : ℝ) (A B : Plane → ℝ) (K1 K2 : ℝ)
    (hA : MemLp A 2 (Cyl.cellμ c)) (hB : MemLp B 2 (Cyl.cellμ c))
    (hK1 : ∫ z in Cyl.cell c, A z ^ 2 ≤ K1) (hK2 : ∫ z in Cyl.cell c, B z ^ 2 ≤ K2) :
    MemLp (fun z => ν * (A z + B z)) 2 (Cyl.cellμ c) ∧
      ∫ z in Cyl.cell c, (ν * (A z + B z)) ^ 2 ≤ 2 * ν ^ 2 * (K1 + K2) := by
  have hMem : MemLp (fun z => ν * (A z + B z)) 2 (Cyl.cellμ c) := (hA.add hB).const_mul ν
  refine ⟨hMem, ?_⟩
  have hI1 : Integrable (fun z => (ν * (A z + B z)) ^ 2) (Cyl.cellμ c) := hMem.integrable_sq
  have hIA : Integrable (fun z => A z ^ 2) (Cyl.cellμ c) := hA.integrable_sq
  have hIB : Integrable (fun z => B z ^ 2) (Cyl.cellμ c) := hB.integrable_sq
  have hI2 : Integrable (fun z => 2 * ν ^ 2 * (A z ^ 2 + B z ^ 2)) (Cyl.cellμ c) :=
    (hIA.add hIB).const_mul (2 * ν ^ 2)
  calc ∫ z in Cyl.cell c, (ν * (A z + B z)) ^ 2
      ≤ ∫ z in Cyl.cell c, 2 * ν ^ 2 * (A z ^ 2 + B z ^ 2) := by
        refine integral_mono hI1 hI2 fun z => ?_
        nlinarith [mul_nonneg (sq_nonneg ν) (sq_nonneg (A z - B z))]
    _ = 2 * ν ^ 2 * ((∫ z in Cyl.cell c, A z ^ 2) + ∫ z in Cyl.cell c, B z ^ 2) := by
        rw [integral_const_mul]
        congr 1
        exact integral_add hIA hIB
    _ ≤ 2 * ν ^ 2 * (K1 + K2) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)

theorem trainLapLocal_of_err (h : UnforcedLeray.Short.PartI.TrainErrJetLocalL2) :
    UnforcedLeray.Short.PartI.TrainLapLocal := by
  intro ν c hν hc tr htr
  obtain ⟨hsm, hloc⟩ := h ν c hν hc tr htr
  have hcomp : ∀ {F : Plane → Vec}, ContDiff ℝ ∞ F → ∀ k : Fin 2,
      ContDiff ℝ ∞ (fun x => F x k) := fun hF k =>
    (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hF
  unfold LocalSmoothJetL2
  refine ⟨fun r hr => ?_, fun s hs => ?_⟩
  · dsimp only
    refine contDiff_euclidean.2 fun k => ?_
    have key : ContDiff ℝ ∞ (fun z => ν * Train.lapS (fun y => trainErr tr r y k) z) :=
      contDiff_const.mul (lapLocal_lapS_contDiff (hcomp (hsm r hr) k))
    have e : ∀ z : Plane, ((ν • Train.vecLaplacian (trainErr tr r)) z) k =
        ν * Train.lapS (fun y => trainErr tr r y k) z := fun z => by
      simp only [Pi.smul_apply, PiLp.smul_apply, smul_eq_mul, lapLocal_vecLap_apply]
    simp only [e]
    exact key
  · unfold LocalJetL2
    intro w k
    obtain ⟨e1, he1, K1, h1⟩ := hloc s hs (true :: true :: w) k
    obtain ⟨e2, he2, K2, h2⟩ := hloc s hs (false :: false :: w) k
    refine ⟨min e1 e2, lt_min he1 he2, 2 * ν ^ 2 * (K1 + K2), fun r hr hrs => ?_⟩
    have hr1 : |r - s| < e1 := lt_of_lt_of_le hrs (min_le_left _ _)
    have hr2 : |r - s| < e2 := lt_of_lt_of_le hrs (min_le_right _ _)
    obtain ⟨m1, i1⟩ := h1 r hr hr1
    obtain ⟨m2, i2⟩ := h2 r hr hr2
    have hk : ContDiff ℝ ∞ (fun y => trainErr tr r y k) := hcomp (hsm r hr) k
    have eq : ∀ z : Plane, wordComp w (fun x => ν • Train.vecLaplacian (trainErr tr r) x) k z =
        ν * (wordComp (true :: true :: w) (trainErr tr r) k z +
          wordComp (false :: false :: w) (trainErr tr r) k z) := by
      intro z
      show wordComp w (fun x => ν • Train.vecLaplacian (trainErr tr r) x) k z = _
      have e1' : (fun x => (ν • Train.vecLaplacian (trainErr tr r) x) k) =
          fun x => ν * Train.lapS (fun y => trainErr tr r y k) x := by
        funext x
        rw [PiLp.smul_apply, smul_eq_mul, lapLocal_vecLap_apply]
      calc wordComp w (fun x => ν • Train.vecLaplacian (trainErr tr r) x) k z
          = B0151.derivWord w (fun x => ν * Train.lapS (fun y => trainErr tr r y k) x) z := by
            unfold wordComp
            rw [e1']
        _ = ν * B0151.derivWord w (fun x => Train.lapS (fun y => trainErr tr r y k) x) z :=
            lapLocal_dw_const_mul ν w _ z
        _ = ν * Train.lapS (B0151.derivWord w (fun y => trainErr tr r y k)) z := by
            rw [JetViscIBP.derivWord_lap w _ hk]
        _ = ν * (wordComp (true :: true :: w) (trainErr tr r) k z +
              wordComp (false :: false :: w) (trainErr tr r) k z) := by
            rw [lapLocal_lapS_dw]
            rfl
    have hw : wordComp w (ν • Train.vecLaplacian (trainErr tr r)) k =
        fun z => ν * (wordComp (true :: true :: w) (trainErr tr r) k z +
          wordComp (false :: false :: w) (trainErr tr r) k z) := funext eq
    dsimp only
    rw [hw]
    exact lapLocal_l2_comb c ν _ _ K1 K2 m1 m2 i1 i2

end UnforcedLeray.Short.PartI
