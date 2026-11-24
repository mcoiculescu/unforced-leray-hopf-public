import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1

/-!
# Part I, task `PartI:T08/4/1/1` (`TrainTimeDerivLocalL2`): decomposition

Source `the November 2 reference manuscript` lines 261-288 (the finite-energy BUC
train, smooth for positive time) and 326-329 (the error equation).

`TrainTimeDerivLocalL2` asks for a uniform `L²(cell)` bound on word derivatives of `∂_r e` for `r`
near `s`, including `r` slightly above `s` when `a(s) = c²`; the pointwise-in-age leaves
(`TrainErrJetL2`, `TrainTimeDerivL2`) need `a ≤ c²` and give no uniformity. The fact is purely one
of positive-time regularity of the finite-energy solution, independent of the width bound, so it
is stated without it.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec Vc pc Qc width)

/-- **Leaf (positive-time `H^∞` regularity of `∂_r e`, locally uniform in time)** (lines 261-288,
326-329): for the finite-energy BUC train, every `s > 0`, word `w` and component `k`, there are
`ε, K` with `∂_w ∂_r e_k(r) ∈ L²(cell)` and `‖·‖₂² ≤ K` for all `r > 0`, `|r - s| < ε`
(no width condition: it follows from parabolic smoothing of the mild solution on `[s/2, 2s]` and
the explicit `V_c^p`; `∂_r e = νΔe - A - ∇π - div Q_c`). -/
def TrainTimeDerivJetLocalAllAges : Prop :=
  ∀ ν c : ℝ, 0 < ν → 1 ≤ c → ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr → ∀ s : ℝ, 0 < s →
    ∀ (w : List Bool) (k : Fin 2), ∃ ε : ℝ, 0 < ε ∧ ∃ K : ℝ,
      ∀ r : ℝ, 0 < r → |r - s| < ε →
        MemLp (wordComp w (fun z => deriv (fun t => trainErr tr t z) r) k) 2 (Cyl.cellμ c) ∧
        ∫ z in Cyl.cell c, (wordComp w (fun z => deriv (fun t => trainErr tr t z) r) k z) ^ 2 ≤ K

/-! ### Decomposition: `∂_r e = νΔe - A - ∇π - div Q_c` with a local uniform `L²` bound on each term -/

/-- A family `F r` (`r > 0`) of meridional fields has, near `s`, every word derivative of every
component in `L²(cell)` with a uniform squared-norm bound. -/
def LocalJetL2 (c : ℝ) (F : ℝ → Plane → Vec) (s : ℝ) : Prop :=
  ∀ (w : List Bool) (k : Fin 2), ∃ ε : ℝ, 0 < ε ∧ ∃ K : ℝ,
    ∀ r : ℝ, 0 < r → |r - s| < ε →
      MemLp (wordComp w (F r) k) 2 (Cyl.cellμ c) ∧
      ∫ z in Cyl.cell c, (wordComp w (F r) k z) ^ 2 ≤ K

/-- Every `F r` (`r > 0`) is smooth, and `LocalJetL2` holds at every `s > 0`. -/
def LocalSmoothJetL2 (c : ℝ) (F : ℝ → Plane → Vec) : Prop :=
  (∀ r : ℝ, 0 < r → ContDiff ℝ ∞ (F r)) ∧ ∀ s : ℝ, 0 < s → LocalJetL2 c F s

/-- **Leaf E (finite-energy regularity of the error, locally uniform in time)** (lines 261-288,
326-329): `e(r) = v(r) - V_c^p(r)` is smooth for every `r > 0` and, near every `s > 0`, its word
derivatives are in `L²(cell)` with uniformly bounded norms (no width condition; parabolic
smoothing of the finite-energy mild solution on `[s/2, 2s]`, and the explicit `V_c^p`). -/
def TrainErrJetLocalL2 : Prop :=
  ∀ ν c : ℝ, 0 < ν → 1 ≤ c → ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr →
    LocalSmoothJetL2 c (fun r => trainErr tr r)

/-- **Leaf E∞ (local sup bounds of the error jets)** (lines 261-288: `IsBUCTrain` bounds the
derivatives of `v` on `[0, S]`; `V_c^p` is explicit): near every `s > 0` every word derivative of
`e(r)` is bounded uniformly. -/
def TrainErrSupLocal : Prop :=
  ∀ ν c : ℝ, 0 < ν → 1 ≤ c → ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr → ∀ s : ℝ, 0 < s →
    ∀ (w : List Bool) (k : Fin 2), ∃ ε : ℝ, 0 < ε ∧ ∃ M : ℝ, ∀ r : ℝ, 0 < r → |r - s| < ε →
      ∀ z : Plane, |wordComp w (trainErr tr r) k z| ≤ M

/-- **Leaf Lap** (a word derivative of `Δe` is a word derivative of `e` of order two higher). -/
def TrainLapLocal : Prop :=
  ∀ ν c : ℝ, 0 < ν → 1 ≤ c → ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr →
    LocalSmoothJetL2 c (fun r => ν • Train.vecLaplacian (trainErr tr r))

/-- **Leaf Adv** (lines 326-329): `A = (V_c·∇)e + (e·∇)V_c + (e·∇)e`, Leibniz on the words with
locally uniform bounds on the jets of `V_c^p`, the local sup bounds and `L²` bounds of `e`. -/
def TrainAdvLocal : Prop :=
  ∀ ν c : ℝ, 0 < ν → 1 ≤ c → ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr →
    LocalSmoothJetL2 c (fun r => advDiff tr r)

/-- **Leaf Q** (lines 326-335): `div Q_c(r)` is smooth with locally uniform `L²(cell)` bounds on
all word derivatives (`Q_c = ∑_{i≠j} V_i ⊗ V_j`, explicit; no width condition). -/
def TrainStressDivLocal : Prop :=
  ∀ ν c : ℝ, 0 < ν → 1 ≤ c → ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr →
    LocalSmoothJetL2 c (fun r => Train.matDiv (Qc ν c r))

/-- **Leaf P** (pressure error, lines 266-270, 326-329): `∇π(r)` is smooth with locally uniform
`L²(cell)` bounds on all word derivatives. (`Δπ = -div(A + div Q_c)` and the contractive
estimate `‖∂_w ∇π‖₂ ≤ ‖∂_w (A + div Q_c)‖₂`.) -/
def TrainPressureGradLocal : Prop :=
  ∀ ν c : ℝ, 0 < ν → 1 ≤ c → ∀ tr : B0140.TrainSol ν c, IsBUCTrain tr →
    LocalSmoothJetL2 c (fun r => Train.gradS (errPressure tr r))

theorem wordMem_sub {c : ℝ} {f g : Plane → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {w : List Bool} (h1 : MemLp (B0151.derivWord w f) 2 (Cyl.cellμ c))
    (h2 : MemLp (B0151.derivWord w g) 2 (Cyl.cellμ c)) :
    MemLp (B0151.derivWord w (fun x => f x - g x)) 2 (Cyl.cellμ c) := by
  have e : B0151.derivWord w (fun x => f x - g x) =
      fun z => B0151.derivWord w f z - B0151.derivWord w g z :=
    funext (derivWord_sub_smooth hf hg w)
  rw [e]
  exact h1.sub h2

theorem trainTimeDerivJetLocalAllAges_of (hX : TrainLapLocal) (hA : TrainAdvLocal)
    (hP : TrainPressureGradLocal) (hQ : TrainStressDivLocal) :
    TrainTimeDerivJetLocalAllAges := by
  intro ν c hν hc tr htr s hs w k
  have hc0 : 0 < c := by linarith
  obtain ⟨sX, jX⟩ := hX ν c hν hc tr htr
  obtain ⟨sA, jA⟩ := hA ν c hν hc tr htr
  obtain ⟨sP, jP⟩ := hP ν c hν hc tr htr
  obtain ⟨sQ, jQ⟩ := hQ ν c hν hc tr htr
  obtain ⟨e1, he1, K1, h1⟩ := jX s hs w k
  obtain ⟨e2, he2, K2, h2⟩ := jA s hs w k
  obtain ⟨e3, he3, K3, h3⟩ := jP s hs w k
  obtain ⟨e4, he4, K4, h4⟩ := jQ s hs w k
  refine ⟨min (min e1 e2) (min e3 e4), by positivity, 4 * (K1 + K2 + K3 + K4), ?_⟩
  intro r hr hrs
  have hr1 : |r - s| < e1 := lt_of_lt_of_le hrs (by simp)
  have hr2 : |r - s| < e2 := lt_of_lt_of_le hrs (by simp)
  have hr3 : |r - s| < e3 := lt_of_lt_of_le hrs (by simp)
  have hr4 : |r - s| < e4 := lt_of_lt_of_le hrs (by simp)
  obtain ⟨m1, i1⟩ := h1 r hr hr1
  obtain ⟨m2, i2⟩ := h2 r hr hr2
  obtain ⟨m3, i3⟩ := h3 r hr hr3
  obtain ⟨m4, i4⟩ := h4 r hr hr4
  have comp : ∀ {F : Plane → Vec}, ContDiff ℝ ∞ F → ∀ k : Fin 2,
      ContDiff ℝ ∞ (fun x => F x k) := fun hF k =>
    (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hF
  have cX := comp (sX r hr) k
  have cA := comp (sA r hr) k
  have cP := comp (sP r hr) k
  have cQ := comp (sQ r hr) k
  have key : (fun z => deriv (fun t => trainErr tr t z) r k) = fun z =>
      (((ν • Train.vecLaplacian (trainErr tr r)) z k - advDiff tr r z k) -
        Train.gradS (errPressure tr r) z k) - Train.matDiv (Qc ν c r) z k := by
    funext z
    have h := TrainErrorEquation.train_error_equation tr hν hc0.ne' r hr z
    have h' := congrArg (fun x : Vec => x k) h
    simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.neg_apply, PiLp.smul_apply] at h'
    simp only [PiLp.smul_apply, PiLp.sub_apply, advDiff, Pi.smul_apply]
    change (deriv (fun t => tr.v t z - Vc ν c t z) r).ofLp k = ν • (Train.vecLaplacian
        (fun w => tr.v r w - Vc ν c r w) z).ofLp k -
        ((Train.advection (tr.v r) z).ofLp k - (Train.advection (Vc ν c r) z).ofLp k) -
        (Train.gradS (errPressure tr r) z).ofLp k - (Train.matDiv (Qc ν c r) z).ofLp k
    change _ = _ - _ - (Train.gradS (fun w => tr.p r w - pc ν c r w) z).ofLp k - _
    linarith
  have e : wordComp w (fun z => deriv (fun t => trainErr tr t z) r) k =
      B0151.derivWord w (fun z => (((ν • Train.vecLaplacian (trainErr tr r)) z k -
        advDiff tr r z k) - Train.gradS (errPressure tr r) z k) -
        Train.matDiv (Qc ν c r) z k) := by
    unfold wordComp
    rw [key]
  rw [e]
  have eqpt : ∀ z, B0151.derivWord w (fun z => (((ν • Train.vecLaplacian (trainErr tr r)) z k -
        advDiff tr r z k) - Train.gradS (errPressure tr r) z k) -
        Train.matDiv (Qc ν c r) z k) z =
      ((wordComp w (ν • Train.vecLaplacian (trainErr tr r)) k z - wordComp w (advDiff tr r) k z) -
        wordComp w (Train.gradS (errPressure tr r)) k z) -
        wordComp w (Train.matDiv (Qc ν c r)) k z := by
    intro z
    rw [derivWord_sub_smooth ((cX.sub cA).sub cP) cQ, derivWord_sub_smooth (cX.sub cA) cP,
      derivWord_sub_smooth cX cA]
    rfl
  have hmem : MemLp (B0151.derivWord w (fun z => (((ν • Train.vecLaplacian (trainErr tr r)) z k -
        advDiff tr r z k) - Train.gradS (errPressure tr r) z k) -
        Train.matDiv (Qc ν c r) z k)) 2 (Cyl.cellμ c) :=
    wordMem_sub ((cX.sub cA).sub cP) cQ
      (by
        have := wordMem_sub (c := c) (cX.sub cA) cP (w := w)
          (wordMem_sub cX cA m1 m2) m3
        exact this) m4
  refine ⟨hmem, ?_⟩
  have s1 := m1.integrable_sq
  have s2 := m2.integrable_sq
  have s3 := m3.integrable_sq
  have s4 := m4.integrable_sq
  have hI : IntegrableOn (fun z => (wordComp w (ν • Train.vecLaplacian (trainErr tr r)) k z) ^ 2)
      (Cyl.cell c) := s1
  have hI2 : IntegrableOn (fun z => (wordComp w (advDiff tr r) k z) ^ 2) (Cyl.cell c) := s2
  have hI3 : IntegrableOn (fun z => (wordComp w (Train.gradS (errPressure tr r)) k z) ^ 2)
      (Cyl.cell c) := s3
  have hI4 : IntegrableOn (fun z => (wordComp w (Train.matDiv (Qc ν c r)) k z) ^ 2)
      (Cyl.cell c) := s4
  have hsum : IntegrableOn (fun z => 4 * ((wordComp w (ν • Train.vecLaplacian (trainErr tr r)) k z) ^ 2
      + (wordComp w (advDiff tr r) k z) ^ 2 + (wordComp w (Train.gradS (errPressure tr r)) k z) ^ 2
      + (wordComp w (Train.matDiv (Qc ν c r)) k z) ^ 2)) (Cyl.cell c) :=
    (((hI.add hI2).add hI3).add hI4).const_mul 4
  have hm : IntegrableOn (fun z => (B0151.derivWord w (fun z => (((ν • Train.vecLaplacian
      (trainErr tr r)) z k - advDiff tr r z k) - Train.gradS (errPressure tr r) z k) -
        Train.matDiv (Qc ν c r) z k) z) ^ 2) (Cyl.cell c) := hmem.integrable_sq
  calc ∫ z in Cyl.cell c, (B0151.derivWord w (fun z => (((ν • Train.vecLaplacian
      (trainErr tr r)) z k - advDiff tr r z k) - Train.gradS (errPressure tr r) z k) -
        Train.matDiv (Qc ν c r) z k) z) ^ 2
      ≤ ∫ z in Cyl.cell c, 4 * ((wordComp w (ν • Train.vecLaplacian (trainErr tr r)) k z) ^ 2
      + (wordComp w (advDiff tr r) k z) ^ 2 + (wordComp w (Train.gradS (errPressure tr r)) k z) ^ 2
      + (wordComp w (Train.matDiv (Qc ν c r)) k z) ^ 2) := by
        refine integral_mono hm hsum fun z => ?_
        simp only [eqpt z]
        nlinarith [sq_nonneg (wordComp w (ν • Train.vecLaplacian (trainErr tr r)) k z
          - wordComp w (advDiff tr r) k z + wordComp w (Train.gradS (errPressure tr r)) k z
          + wordComp w (Train.matDiv (Qc ν c r)) k z),
          sq_nonneg (wordComp w (ν • Train.vecLaplacian (trainErr tr r)) k z
          - wordComp w (advDiff tr r) k z - wordComp w (Train.gradS (errPressure tr r)) k z
          - wordComp w (Train.matDiv (Qc ν c r)) k z),
          sq_nonneg (wordComp w (ν • Train.vecLaplacian (trainErr tr r)) k z
          + wordComp w (advDiff tr r) k z),
          sq_nonneg (wordComp w (Train.gradS (errPressure tr r)) k z
          + wordComp w (Train.matDiv (Qc ν c r)) k z),
          sq_nonneg (wordComp w (ν • Train.vecLaplacian (trainErr tr r)) k z
          - wordComp w (advDiff tr r) k z),
          sq_nonneg (wordComp w (Train.gradS (errPressure tr r)) k z
          - wordComp w (Train.matDiv (Qc ν c r)) k z)]
    _ = 4 * ((∫ z in Cyl.cell c, (wordComp w (ν • Train.vecLaplacian (trainErr tr r)) k z) ^ 2)
      + (∫ z in Cyl.cell c, (wordComp w (advDiff tr r) k z) ^ 2)
      + (∫ z in Cyl.cell c, (wordComp w (Train.gradS (errPressure tr r)) k z) ^ 2)
      + (∫ z in Cyl.cell c, (wordComp w (Train.matDiv (Qc ν c r)) k z) ^ 2)) := by
        have i12 : IntegrableOn (fun z => (wordComp w (ν • Train.vecLaplacian (trainErr tr r)) k z) ^ 2
            + (wordComp w (advDiff tr r) k z) ^ 2) (Cyl.cell c) := hI.add hI2
        have i123 : IntegrableOn (fun z => (wordComp w (ν • Train.vecLaplacian (trainErr tr r)) k z) ^ 2
            + (wordComp w (advDiff tr r) k z) ^ 2
            + (wordComp w (Train.gradS (errPressure tr r)) k z) ^ 2) (Cyl.cell c) := i12.add hI3
        rw [integral_const_mul, integral_add i123 hI4, integral_add i12 hI3, integral_add hI hI2]
    _ ≤ 4 * (K1 + K2 + K3 + K4) := by linarith

theorem trainTimeDerivLocalL2_of (h : TrainTimeDerivJetLocalAllAges) : TrainTimeDerivLocalL2 :=
  fun ν c hν hc tr htr s hs _ w k => h ν c hν hc tr htr s hs w k

end UnforcedLeray.Short.PartI
