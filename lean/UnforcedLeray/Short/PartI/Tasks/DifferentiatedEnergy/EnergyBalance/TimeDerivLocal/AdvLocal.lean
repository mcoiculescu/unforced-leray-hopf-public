import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1_1
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.EnergyBalance.TimeDerivLocal.ErrSupLocal
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.PressureRegular.TrainAdvDiffL2.Leibniz
import UnforcedLeray.Lib.TrainB.SmoothProduct

/-!
# Part I, task `PartI:T08/4/1/1/4` (`TrainAdvLocal`): proof

Source `the November 2 reference manuscript` lines 326-329.

`A = (V_c·∇)e + (e·∇)V_c + (e·∇)e` has components that are sums of six products of a factor with
locally uniformly bounded word derivatives and a factor with locally uniformly `L²`-bounded word
derivatives. The class `Gps` of such finite sums (relative to a time `s`) is closed under
coordinate derivatives (one-step Leibniz), hence under words, and its members have a local
uniform `L²` bound.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec Vc pc Qc width)

namespace AdvLoc

/-- Time-parametrized family, smooth for `r > 0`, word derivatives bounded locally uniformly
near `s`. -/
def BWf (s : ℝ) (F : ℝ → Plane → ℝ) : Prop :=
  (∀ r : ℝ, 0 < r → ContDiff ℝ ∞ (F r)) ∧
    ∀ w : List Bool, ∃ ε : ℝ, 0 < ε ∧ ∃ M : ℝ, ∀ r : ℝ, 0 < r → |r - s| < ε →
      ∀ z : Plane, |B0151.derivWord w (F r) z| ≤ M

/-- Time-parametrized family, smooth for `r > 0`, word derivatives in `L²(cell)` with locally
uniform squared norms near `s`. -/
def LWf (c s : ℝ) (G : ℝ → Plane → ℝ) : Prop :=
  (∀ r : ℝ, 0 < r → ContDiff ℝ ∞ (G r)) ∧
    ∀ w : List Bool, ∃ ε : ℝ, 0 < ε ∧ ∃ K : ℝ, ∀ r : ℝ, 0 < r → |r - s| < ε →
      MemLp (B0151.derivWord w (G r)) 2 (Cyl.cellμ c) ∧
      ∫ z in Cyl.cell c, (B0151.derivWord w (G r) z) ^ 2 ≤ K

theorem BWf.deriv {s : ℝ} {F : ℝ → Plane → ℝ} (hF : BWf s F) (b : Bool) :
    BWf s (fun r => B0151.derivWord [b] (F r)) := by
  refine ⟨fun r hr => B0151.contDiff_derivWord (hF.1 r hr) [b], fun w => ?_⟩
  obtain ⟨ε, hε, M, hM⟩ := hF.2 (w ++ [b])
  refine ⟨ε, hε, M, fun r hr hrs z => ?_⟩
  have := hM r hr hrs z
  rw [AdvLeib.derivWord_append] at this
  exact this

theorem LWf.deriv {c s : ℝ} {G : ℝ → Plane → ℝ} (hG : LWf c s G) (b : Bool) :
    LWf c s (fun r => B0151.derivWord [b] (G r)) := by
  refine ⟨fun r hr => B0151.contDiff_derivWord (hG.1 r hr) [b], fun w => ?_⟩
  obtain ⟨ε, hε, K, hK⟩ := hG.2 (w ++ [b])
  refine ⟨ε, hε, K, fun r hr hrs => ?_⟩
  have := hK r hr hrs
  rw [AdvLeib.derivWord_append] at this
  exact this

/-- Finite sums of products. -/
inductive Gps (c s : ℝ) : (ℝ → Plane → ℝ) → Prop
  | prod {F G : ℝ → Plane → ℝ} : BWf s F → LWf c s G → Gps c s (fun r z => F r z * G r z)
  | add {A B : ℝ → Plane → ℝ} : Gps c s A → Gps c s B → Gps c s (fun r z => A r z + B r z)

theorem Gps.smooth {c s : ℝ} {H : ℝ → Plane → ℝ} (hH : Gps c s H) :
    ∀ r : ℝ, 0 < r → ContDiff ℝ ∞ (H r) := by
  induction hH with
  | prod hf hg => exact fun r hr => (hf.1 r hr).mul (hg.1 r hr)
  | add _ _ ih1 ih2 => exact fun r hr => (ih1 r hr).add (ih2 r hr)

theorem Gps.deriv {c s : ℝ} {H : ℝ → Plane → ℝ} (hH : Gps c s H) (b : Bool) :
    ∃ H' : ℝ → Plane → ℝ, Gps c s H' ∧
      ∀ r : ℝ, 0 < r → ∀ z : Plane, H' r z = B0151.derivWord [b] (H r) z := by
  induction hH with
  | @prod F G hf hg =>
      refine ⟨fun r z => B0151.derivWord [b] (F r) z * G r z +
        F r z * B0151.derivWord [b] (G r) z,
        Gps.add (Gps.prod (hf.deriv b) hg) (Gps.prod hf (hg.deriv b)), fun r hr z => ?_⟩
      rw [TrainB.derivWord_singleton_mul (hf.1 r hr) (hg.1 r hr) b]
  | @add A B h1 h2 ih1 ih2 =>
      obtain ⟨A', hA', eA⟩ := ih1
      obtain ⟨B', hB', eB⟩ := ih2
      refine ⟨fun r z => A' r z + B' r z, Gps.add hA' hB', fun r hr z => ?_⟩
      rw [TrainB.derivWord_singleton_add (h1.smooth r hr) (h2.smooth r hr) b]
      show A' r z + B' r z = _
      rw [eA r hr z, eB r hr z]

theorem Gps.word {c s : ℝ} {H : ℝ → Plane → ℝ} (hH : Gps c s H) :
    ∀ w : List Bool, ∃ H' : ℝ → Plane → ℝ, Gps c s H' ∧
      ∀ r : ℝ, 0 < r → ∀ z : Plane, H' r z = B0151.derivWord w (H r) z
  | [] => ⟨H, hH, fun r hr z => rfl⟩
  | b :: w => by
      obtain ⟨H1, h1, e1⟩ := Gps.word hH w
      obtain ⟨H2, h2, e2⟩ := h1.deriv b
      refine ⟨H2, h2, fun r hr z => ?_⟩
      rw [e2 r hr z]
      have : H1 r = B0151.derivWord w (H r) := funext (e1 r hr)
      rw [this]
      cases b <;> rfl

theorem Gps.l2 {c s : ℝ} {H : ℝ → Plane → ℝ} (hH : Gps c s H) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ K : ℝ, ∀ r : ℝ, 0 < r → |r - s| < ε →
      MemLp (H r) 2 (Cyl.cellμ c) ∧ ∫ z in Cyl.cell c, (H r z) ^ 2 ≤ K := by
  induction hH with
  | @prod F G hf hg =>
      obtain ⟨e1, he1, M, hM⟩ := hf.2 []
      obtain ⟨e2, he2, K, hK⟩ := hg.2 []
      refine ⟨min e1 e2, lt_min he1 he2, M ^ 2 * K, fun r hr hrs => ?_⟩
      have hr1 : |r - s| < e1 := lt_of_lt_of_le hrs (min_le_left _ _)
      have hr2 : |r - s| < e2 := lt_of_lt_of_le hrs (min_le_right _ _)
      obtain ⟨m, i⟩ := hK r hr hr2
      change MemLp (G r) 2 (Cyl.cellμ c) at m
      change ∫ z in Cyl.cell c, (G r z) ^ 2 ≤ K at i
      have hb : ∀ z, |F r z| ≤ M := fun z => hM r hr hr1 z
      have hmem : MemLp (fun z => F r z * G r z) 2 (Cyl.cellμ c) := by
        refine MemLp.of_le_mul (c := M) m
          (((hf.1 r hr).continuous.mul (hg.1 r hr).continuous).aestronglyMeasurable) ?_
        refine Filter.Eventually.of_forall fun z => ?_
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hb z) (abs_nonneg _)
      refine ⟨hmem, ?_⟩
      have hI1 : Integrable (fun z => (F r z * G r z) ^ 2) (Cyl.cellμ c) := hmem.integrable_sq
      have hIG : Integrable (fun z => (G r z) ^ 2) (Cyl.cellμ c) := m.integrable_sq
      have hI2 : Integrable (fun z => M ^ 2 * (G r z) ^ 2) (Cyl.cellμ c) :=
        hIG.const_mul (M ^ 2)
      calc ∫ z in Cyl.cell c, (F r z * G r z) ^ 2
          ≤ ∫ z in Cyl.cell c, M ^ 2 * (G r z) ^ 2 := by
            refine integral_mono hI1 hI2 fun z => ?_
            have h1 : (F r z) ^ 2 ≤ M ^ 2 := by
              have := sq_abs (F r z)
              nlinarith [hb z, abs_nonneg (F r z)]
            calc (F r z * G r z) ^ 2 = (F r z) ^ 2 * (G r z) ^ 2 := by ring
              _ ≤ M ^ 2 * (G r z) ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
        _ = M ^ 2 * ∫ z in Cyl.cell c, (G r z) ^ 2 := integral_const_mul _ _
        _ ≤ M ^ 2 * K := mul_le_mul_of_nonneg_left i (sq_nonneg _)
  | @add A B h1 h2 ih1 ih2 =>
      obtain ⟨e1, he1, K1, hK1⟩ := ih1
      obtain ⟨e2, he2, K2, hK2⟩ := ih2
      refine ⟨min e1 e2, lt_min he1 he2, 2 * (K1 + K2), fun r hr hrs => ?_⟩
      have hr1 : |r - s| < e1 := lt_of_lt_of_le hrs (min_le_left _ _)
      have hr2 : |r - s| < e2 := lt_of_lt_of_le hrs (min_le_right _ _)
      obtain ⟨mA, iA⟩ := hK1 r hr hr1
      obtain ⟨mB, iB⟩ := hK2 r hr hr2
      have hmem : MemLp (fun z => A r z + B r z) 2 (Cyl.cellμ c) := mA.add mB
      refine ⟨hmem, ?_⟩
      have hI1 : Integrable (fun z => (A r z + B r z) ^ 2) (Cyl.cellμ c) := hmem.integrable_sq
      have hIA : Integrable (fun z => (A r z) ^ 2) (Cyl.cellμ c) := mA.integrable_sq
      have hIB : Integrable (fun z => (B r z) ^ 2) (Cyl.cellμ c) := mB.integrable_sq
      have hI2 : Integrable (fun z => 2 * ((A r z) ^ 2 + (B r z) ^ 2)) (Cyl.cellμ c) :=
        (hIA.add hIB).const_mul 2
      calc ∫ z in Cyl.cell c, (A r z + B r z) ^ 2
          ≤ ∫ z in Cyl.cell c, 2 * ((A r z) ^ 2 + (B r z) ^ 2) := by
            refine integral_mono hI1 hI2 fun z => ?_
            nlinarith [sq_nonneg (A r z - B r z)]
        _ = 2 * ((∫ z in Cyl.cell c, (A r z) ^ 2) + ∫ z in Cyl.cell c, (B r z) ^ 2) := by
            rw [integral_const_mul]
            congr 1
            exact integral_add hIA hIB
        _ ≤ 2 * (K1 + K2) := mul_le_mul_of_nonneg_left (by linarith) (by norm_num)

/-- Transfer of the local `L²` bound along a pointwise identity valid for `r > 0`. -/
theorem Gps.jet {c s : ℝ} {H H1 : ℝ → Plane → ℝ} (hH : Gps c s H)
    (hE : ∀ r : ℝ, 0 < r → ∀ z : Plane, H r z = H1 r z) (w : List Bool) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ K : ℝ, ∀ r : ℝ, 0 < r → |r - s| < ε →
      MemLp (B0151.derivWord w (H1 r)) 2 (Cyl.cellμ c) ∧
      ∫ z in Cyl.cell c, (B0151.derivWord w (H1 r) z) ^ 2 ≤ K := by
  obtain ⟨H', hH', e'⟩ := hH.word w
  obtain ⟨ε, hε, K, hK⟩ := hH'.l2
  refine ⟨ε, hε, K, fun r hr hrs => ?_⟩
  have hf : H r = H1 r := funext (hE r hr)
  have : B0151.derivWord w (H1 r) = H' r := by
    funext z
    rw [e' r hr z, hf]
  rw [this]
  exact hK r hr hrs

end AdvLoc

open AdvLoc in
theorem trainAdvLocal_of (h1 : UnforcedLeray.Short.PartI.TrainErrJetLocalL2)
    (h2 : UnforcedLeray.Short.PartI.TrainErrSupLocal) :
    UnforcedLeray.Short.PartI.TrainAdvLocal := by
  intro ν c hν hc tr htr
  have hc0 : 0 < c := by linarith
  obtain ⟨hsm, hloc⟩ := h1 ν c hν hc tr htr
  have comp : ∀ {F : Plane → Vec}, ContDiff ℝ ∞ F → ∀ k : Fin 2,
      ContDiff ℝ ∞ (fun x => F x k) := fun hF k =>
    (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hF
  have hv : ∀ r : ℝ, 0 < r → ContDiff ℝ ∞ (tr.v r) := fun r hr =>
    TrainErrorEquation.contDiff_slice tr.isTrain.smooth_v hr.le
  have hVs : ∀ r : ℝ, 0 < r → ContDiff ℝ ∞ (Vc ν c r) := fun r hr => vcSmoothPos ν c hν hc0 r hr
  -- the families, for a fixed time `s`
  have main : ∀ s : ℝ, 0 < s → ∀ k : Fin 2, ∃ H : ℝ → Plane → ℝ, Gps c s H ∧
      ∀ r : ℝ, 0 < r → ∀ z : Plane, H r z = advDiff tr r z k := by
    intro s hs k
    have Be : ∀ k : Fin 2, BWf s (fun r x => trainErr tr r x k) := fun k =>
      ⟨fun r hr => comp (hsm r hr) k, fun w => h2 ν c hν hc tr htr s hs w k⟩
    have Le : ∀ k : Fin 2, LWf c s (fun r x => trainErr tr r x k) := fun k =>
      ⟨fun r hr => comp (hsm r hr) k, fun w => hloc s hs w k⟩
    have BV : ∀ k : Fin 2, BWf s (fun r x => Vc ν c r x k) := fun k =>
      ⟨fun r hr => comp (hVs r hr) k, fun w => vcWordSupLocal ν c hν hc s hs w k⟩
    refine ⟨fun r z =>
      Vc ν c r z 0 * B0151.derivWord [true] (fun x => trainErr tr r x k) z +
      Vc ν c r z 1 * B0151.derivWord [false] (fun x => trainErr tr r x k) z +
      B0151.derivWord [true] (fun x => Vc ν c r x k) z * trainErr tr r z 0 +
      B0151.derivWord [false] (fun x => Vc ν c r x k) z * trainErr tr r z 1 +
      trainErr tr r z 0 * B0151.derivWord [true] (fun x => trainErr tr r x k) z +
      trainErr tr r z 1 * B0151.derivWord [false] (fun x => trainErr tr r x k) z, ?_, ?_⟩
    · exact Gps.add (Gps.add (Gps.add (Gps.add (Gps.add
        (Gps.prod (BV 0) ((Le k).deriv true)) (Gps.prod (BV 1) ((Le k).deriv false)))
        (Gps.prod ((BV k).deriv true) (Le 0))) (Gps.prod ((BV k).deriv false) (Le 1)))
        (Gps.prod (Be 0) ((Le k).deriv true))) (Gps.prod (Be 1) ((Le k).deriv false))
    · intro r hr z
      have hd : ∀ (b : Bool) (j : Fin 2) (z : Plane),
          B0151.derivWord [b] (fun x => trainErr tr r x j) z =
            B0151.derivWord [b] (fun x => tr.v r x j) z -
              B0151.derivWord [b] (fun x => Vc ν c r x j) z :=
        fun b j z => derivWord_sub_smooth (comp (hv r hr) j) (comp (hVs r hr) j) [b] z
      beta_reduce
      rw [hd true k z, hd false k z]
      fin_cases k
      · simp [advDiff, Train.advection, trainErr, B0151.derivWord]
        change _ = _
        have e1 : ∀ f : Plane → ℝ, ∀ z, Cyl.partialQ f z = GaussianVortex.partialX f z :=
          fun _ _ => rfl
        have e2 : ∀ f : Plane → ℝ, ∀ z, Cyl.partialEta f z = GaussianVortex.partialY f z :=
          fun _ _ => rfl
        simp only [e1, e2]
        ring
      · simp [advDiff, Train.advection, trainErr, B0151.derivWord]
        change _ = _
        have e1 : ∀ f : Plane → ℝ, ∀ z, Cyl.partialQ f z = GaussianVortex.partialX f z :=
          fun _ _ => rfl
        have e2 : ∀ f : Plane → ℝ, ∀ z, Cyl.partialEta f z = GaussianVortex.partialY f z :=
          fun _ _ => rfl
        simp only [e1, e2]
        ring
  unfold LocalSmoothJetL2
  refine ⟨fun r hr => ?_, fun s hs => ?_⟩
  · dsimp only
    refine contDiff_euclidean.2 fun k => ?_
    obtain ⟨H, hH, eH⟩ := main r hr k
    have := hH.smooth r hr
    have e : H r = fun z => advDiff tr r z k := funext (eH r hr)
    rw [e] at this
    exact this
  · intro w k
    obtain ⟨H, hH, eH⟩ := main s hs k
    exact hH.jet (H1 := fun r z => advDiff tr r z k) eH w

end UnforcedLeray.Short.PartI
