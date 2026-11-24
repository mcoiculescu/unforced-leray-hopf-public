import UnforcedLeray.Short.PartI.Sub.T04.APriori
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.MildTrainExists
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.HkPersistence
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.SpatialRepFromPersistent
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.TimeSmoothLeray
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.LerayVelocityToClassical
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.FiniteEnergyDecay
import UnforcedLeray.Short.PartI.Sub.T02.LerayPressureGauge
import UnforcedLeray.Short.PartI.Sub.T02.ClassicalOdd
import UnforcedLeray.Short.PartI.Sub.T02.VorticityFirstMoment
import UnforcedLeray.Short.PartI.Sub.T02.StreamExists
import UnforcedLeray.Short.PartI.StatementsTrain
import UnforcedLeray.Lib.TrainB.P0CompactMildEquationRestriction

/-!
# Part I, task `PartI:T04`: global existence of the BUC train (conditional composition)

Source of record: `the November 2 reference manuscript`, lines 261-288
(Gallay-Slijepčević 2015, Theorem 1.1 and Remark 1.3(2): "a unique global mild solution in `BUC`,
smooth for positive time, with the bounded periodic pressure choice", lines 270-277; the
finite-energy solution and the energy identities, lines 278-287; uniqueness and oddness, line 288).

`trainGlobalExistence_of` derives `TrainGlobalExistence` (`StatementsTrain.lean`) from the five
leaf statements of `Defs.lean` / `APriori.lean`:

* `mildTrainH3APriori_of`: the a priori `H³` bound of mild trains, through the classical solution
  of the `PartI:T02/1` chain (`classical_of_mild`), `JetL2FromPersistent`, `ClassicalH3APriori` and
  `H3NormOfRep`;
* `mildTrainGlobal_of`: continuation of the mild train to every `[0,S]` by the uniform restart time
  of the `H³` ball (`TrainB.exists_uniform_short_projected_mild_train_on_P0_ball`), `MildConcat` and
  restriction (`TrainB.compactMildEquation_restrict`);
* `trainClassicalOnEvery_of`: the `PartI:T02` chain (`hkPersistence` ... `streamExists`, all proved
  for an arbitrary interval) on `[0,S]`;
* `trainGlobal_of_every`: gluing the trains on `[0, n+1]` (`TrainOnUnique`) into a global
  `B0140.TrainSol` of the class `IsBUCTrain`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.B0140 (trainDatum)
open UnforcedLeray.TrainB

/-! ### From a mild train to a classical solution on the same interval -/

/-- The `PartI:T02/1` chain on an arbitrary `[0,T]`: a mild train has a smooth representative
which, with a decaying pressure, is a classical solution with bounded derivatives. -/
theorem classical_of_mild {ν c T : ℝ} (hν : 0 < ν) (hc : 0 < c) (hc1 : 1 ≤ c) (hT : 0 < T)
    (u : ContinuousMap (Icc (0 : ℝ) T) (VectorH3 c)) (hu : IsMildTrain ν c T hν hc hc1 hT u) :
    ∃ (w : ℝ → Plane → Vec) (p : ℝ → Plane → ℝ), IsSpatialRepOn c T u w ∧
      PersistentFamily c T u ∧ IsClassicalOn ν c T w p ∧ HasBoundedDerivsOn T w ∧
      VelocityDecayOn T w ∧ PressureDecayOn T p := by
  have hk := hkPersistence ν c T hν hc hc1 hT u hu
  obtain ⟨w, hw⟩ := spatialRepFromPersistent ν c T hν hc hc1 hT u hu hk
  have hL := timeSmoothLeray ν c T hν hc hc1 hT u hu w hw
  obtain ⟨p, hps, hpp, hpm⟩ := lerayVelocityToClassical ν c T w hν hc1 hT hL
  have hcl : IsClassicalOn ν c T w p :=
    { smooth_v := hL.smooth_v
      smooth_p := hps
      periodic_v := hL.periodic_v
      periodic_p := hpp
      solenoidal := hL.solenoidal
      momentum := hpm
      initial := hL.initial
      finite_energy := hL.finite_energy }
  have hdec : VelocityDecayOn T w :=
    finiteEnergyDecay c T w hc hL.periodic_v
      (fun s hs => (hw.smooth s hs).differentiable (by simp)) hL.bounded hL.finite_energy
  obtain ⟨p', hcl', hp'⟩ := lerayPressureGauge ν c T w p hν hc1 hT hcl hL.bounded hdec
  exact ⟨w, p', hw, hk, hcl', hL.bounded, hdec, hp'⟩

/-- **The a priori `H³` bound of mild trains** from the bridges and the classical a priori bound. -/
theorem mildTrainH3APriori_of (hN : H3NormOfRep) (hJ : JetL2FromPersistent)
    (hAP : ClassicalH3APriori) : MildTrainH3APriori := by
  intro ν c hν hc hc1 S hS
  obtain ⟨K, -, hK⟩ := hN
  obtain ⟨B, hB⟩ := hAP ν c S hν hc1 hS
  refine ⟨Real.sqrt (K * B), ?_⟩
  intro T hT hTS u hu t
  obtain ⟨w, p, hw, hpers, hcl, hb, -, hpd⟩ := classical_of_mild hν hc hc1 hT u hu
  have hjet : JetL2On c T w := hJ c T u w hc hc1 hT hpers hw
  have hcls : IsAPrioriClass ν c T w p := ⟨hT, hcl, hb, hpd, hjet⟩
  have hbd := hK c T u w B hc hw (fun s hs j hj => by
    obtain ⟨Kj, hKj⟩ := hjet j
    exact ⟨(hKj s hs).1, hB T w p hcls hTS s hs j hj⟩)
  exact Real.le_sqrt_of_sq_le (hbd t)

/-! ### Continuation of the mild train -/

/-- Restriction of a mild train to a shorter interval (`TrainB.compactMildEquation_restrict`). -/
theorem mildTrainOn_mono {ν c T T' : ℝ} {hν : 0 < ν} {hc : 0 < c} {hc1 : 1 ≤ c}
    (hT' : 0 < T') (hT'T : T' ≤ T) (h : MildTrainOn ν c T hν hc hc1) :
    MildTrainOn ν c T' hν hc hc1 := by
  obtain ⟨hT, u, hfix, hP0, htr⟩ := h
  refine ⟨hT', restrictCompactEvolutionPath hT'T u, ?_, fun t => hP0 _, htr⟩
  refine (compactMildEquation_restrict hc hc1 hν hT'.le hT.le hT'T _ u hfix).trans ?_
  congr 1

/-- **Continuation** (lines 270-277): the mild train exists on every `[0,S]`. -/
theorem mildTrainGlobal_of (hC : MildConcat) (hA : MildTrainH3APriori) : MildTrainGlobal := by
  intro ν c hν hc hc1 S hS
  obtain ⟨M, hM⟩ := hA ν c hν hc hc1 S hS
  obtain ⟨τ, hτ, hrestart⟩ :=
    exists_uniform_short_projected_mild_train_on_P0_ball hc hc1 hν (le_max_right M 0)
  have hext : ∀ T : ℝ, T ≤ S → MildTrainOn ν c T hν hc hc1 →
      MildTrainOn ν c (T + τ) hν hc hc1 := by
    rintro T hTS ⟨hT, u, hfix, hP0, htr⟩
    have hy : ‖u ⟨T, hT.le, le_rfl⟩‖ ≤ max M 0 :=
      (hM T hT hTS u ⟨hfix, hP0, htr⟩ _).trans (le_max_left _ _)
    obtain ⟨u₂, -, hfix₂, hP0₂, htr₂, -⟩ := hrestart _ hy (hP0 _)
    obtain ⟨w, hw1, hw2, hw3⟩ := hC ν c T τ hν hc hc1 hT hτ (projectedInitialDatumH3 hc) u u₂
      (P0H3CLM_idem hc (datumVecH3 hc)) hfix hP0 htr hfix₂ hP0₂ htr₂
    exact ⟨add_pos hT hτ, w, hw1, hw2, hw3⟩
  obtain ⟨T₀, hT₀, u₀, hu₀⟩ := mildTrainExists ν c hν hc hc1
  have hT₁ : 0 < min T₀ S := lt_min hT₀ hS
  have hP₁ : MildTrainOn ν c (min T₀ S) hν hc hc1 :=
    mildTrainOn_mono hT₁ (min_le_left _ _) ⟨hT₀, u₀, hu₀⟩
  have hind : ∀ n : ℕ, MildTrainOn ν c (min S (min T₀ S + (n : ℝ) * τ)) hν hc hc1 := by
    intro n
    induction n with
    | zero =>
      have e : min S (min T₀ S + ((0 : ℕ) : ℝ) * τ) = min T₀ S := by
        rw [Nat.cast_zero, zero_mul, add_zero]
        exact min_eq_right (min_le_right _ _)
      rw [e]
      exact hP₁
    | succ n ih =>
      have hpos : 0 < min S (min T₀ S + ((n + 1 : ℕ) : ℝ) * τ) :=
        lt_min hS (add_pos_of_pos_of_nonneg hT₁ (mul_nonneg (Nat.cast_nonneg _) hτ.le))
      refine mildTrainOn_mono hpos ?_ (hext _ (min_le_left _ _) ih)
      rw [Nat.cast_succ]
      rcases le_total S (min T₀ S + (n : ℝ) * τ) with h | h
      · rw [min_eq_left h]
        exact (min_le_left _ _).trans (by linarith)
      · rw [min_eq_right h]
        exact (min_le_right _ _).trans (le_of_eq (by ring))
  obtain ⟨n, hn⟩ := exists_nat_gt (S / τ)
  have hge : S ≤ min T₀ S + (n : ℝ) * τ := by
    have h' : S < (n : ℝ) * τ := by rwa [div_lt_iff₀ hτ] at hn
    linarith [hT₁.le]
  have h := hind n
  rw [min_eq_left hge] at h
  obtain ⟨_, u, hu⟩ := h
  exact ⟨u, hu⟩

/-! ### The classical train on every finite interval -/

/-- The `PartI:T02` chain on `[0,S]`, for every `S > 0`. -/
theorem trainClassicalOnEvery_of (h : MildTrainGlobal) : TrainClassicalOnEvery := by
  intro ν c hν hc1 S hS
  have hc : 0 < c := lt_of_lt_of_le one_pos hc1
  obtain ⟨u, hu⟩ := h ν c hν hc hc1 S hS
  obtain ⟨w, p, -, -, hcl, hb, -, hp⟩ := classical_of_mild hν hc hc1 hS u hu
  have hodd : IsOddOn S w := classicalOdd ν c S w p hν hc1 hS hcl hb hp
  have hmom : VorticityMomentOn c S w := vorticityFirstMoment ν c S w p hν hc1 hS hcl hb
  obtain ⟨ψ, hψ⟩ := streamExists ν c S w p hν hc1 hS hcl hb hodd hmom
  exact ⟨w, p, ψ,
    { smooth_v := hcl.smooth_v
      smooth_p := hcl.smooth_p
      periodic_v := hcl.periodic_v
      periodic_p := hcl.periodic_p
      solenoidal := hcl.solenoidal
      momentum := hcl.momentum
      initial := hcl.initial
      finite_energy := hcl.finite_energy
      pressure_decay := hp
      stream_differentiable := fun s hs => (hψ s hs).1
      stream := fun s hs => (hψ s hs).2.1
      stream_decay := fun s hs => (hψ s hs).2.2
      odd := hodd }, hb⟩

/-! ### Gluing along the ages -/

/-- At age `s`, the `⌈s⌉₊`-th member of a sequence of fields (defined on `[0, ⌈s⌉₊ + 1]`). -/
def glueAge {F : Type*} (G : ℕ → ℝ → Plane → F) : ℝ → Plane → F := fun s => G ⌈s⌉₊ s

theorem le_ceil_add_one (s : ℝ) : s ≤ (⌈s⌉₊ : ℝ) + 1 := by
  linarith [Nat.le_ceil s]

/-- Joint smoothness of a glued field on `[0,∞) × ℝ²` from smoothness of its members on
`[0, n+1] × ℝ²` (smoothness is local). -/
theorem contDiffOn_glueAge {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : ℕ → ℝ → Plane → F)
    (hG : ∀ n : ℕ,
      ContDiffOn ℝ ∞ (fun x : ℝ × Plane => G n x.1 x.2) (Icc 0 ((n : ℝ) + 1) ×ˢ univ))
    (hag : ∀ (n : ℕ) (s : ℝ), 0 ≤ s → s ≤ (n : ℝ) + 1 → glueAge G s = G n s) :
    ContDiffOn ℝ ∞ (fun x : ℝ × Plane => glueAge G x.1 x.2) (Ici 0 ×ˢ univ) := by
  apply contDiffOn_of_locally_contDiffOn
  intro x _
  refine ⟨Iio ((⌈x.1⌉₊ : ℝ) + 1) ×ˢ univ, isOpen_Iio.prod isOpen_univ,
    ⟨show x.1 < (⌈x.1⌉₊ : ℝ) + 1 by linarith [Nat.le_ceil x.1], mem_univ _⟩, ?_⟩
  refine ((hG ⌈x.1⌉₊).mono ?_).congr ?_
  · rintro ⟨s, z⟩ ⟨⟨hs, -⟩, hs', -⟩
    exact ⟨⟨hs, le_of_lt hs'⟩, mem_univ _⟩
  · rintro ⟨s, z⟩ ⟨⟨hs, -⟩, hs', -⟩
    exact congrFun (hag ⌈x.1⌉₊ s hs (le_of_lt hs')) z

/-- **Gluing** (line 276, the global solution; line 288, uniqueness): bounded classical trains on
every `[0,S]` give a global train of the BUC class. -/
theorem trainGlobal_of_every (hU : TrainOnUnique) (h : TrainClassicalOnEvery) :
    TrainGlobalExistence := by
  intro ν c hν hc1
  have hn : ∀ n : ℕ, ∃ (v : ℝ → Plane → Vec) (p ψ : ℝ → Plane → ℝ),
      IsTrainOn ν c ((n : ℝ) + 1) v p ψ ∧ HasBoundedDerivsOn ((n : ℝ) + 1) v :=
    fun n => h ν c hν hc1 ((n : ℝ) + 1) (by positivity)
  choose V P Ψ hV hB using hn
  have hag : ∀ (n : ℕ) (s : ℝ), 0 ≤ s → s ≤ (n : ℝ) + 1 →
      glueAge V s = V n s ∧ glueAge P s = P n s ∧ glueAge Ψ s = Ψ n s := by
    intro n s hs hsn
    exact hU ν c _ _ (V ⌈s⌉₊) (V n) (P ⌈s⌉₊) (P n) (Ψ ⌈s⌉₊) (Ψ n) hν hc1 (by positivity)
      (by positivity) (hV _) (hV n) (hB _) (hB n) s hs (le_ceil_add_one s) hsn
  have hmom : ∀ s : ℝ, 0 < s → ∀ z,
      Train.momentumResidual ν (glueAge V) (glueAge P) s z = 0 := by
    intro s hs z
    have hsn : s < (⌈s⌉₊ : ℝ) + 1 := by linarith [Nat.le_ceil s]
    have hev : (fun t => glueAge V t z) =ᶠ[𝓝 s] (fun t => V ⌈s⌉₊ t z) := by
      filter_upwards [Ioo_mem_nhds hs hsn] with t ht
      exact congrFun (hag ⌈s⌉₊ t ht.1.le ht.2.le).1 z
    have h0 := (hV ⌈s⌉₊).momentum s ⟨hs, hsn⟩ z
    unfold Train.momentumResidual at h0 ⊢
    rw [hev.deriv_eq]
    exact h0
  have hT : B0140.IsTrain ν c (glueAge V) (glueAge P) (glueAge Ψ) :=
    { smooth_v := contDiffOn_glueAge V (fun n => (hV n).smooth_v)
        (fun n s hs hsn => (hag n s hs hsn).1)
      smooth_p := contDiffOn_glueAge P (fun n => (hV n).smooth_p)
        (fun n s hs hsn => (hag n s hs hsn).2.1)
      periodic_v := fun s hs => (hV ⌈s⌉₊).periodic_v s ⟨hs, le_ceil_add_one s⟩
      periodic_p := fun s hs => (hV ⌈s⌉₊).periodic_p s ⟨hs, le_ceil_add_one s⟩
      solenoidal := fun s hs => (hV ⌈s⌉₊).solenoidal s ⟨hs, le_ceil_add_one s⟩
      momentum := hmom
      initial := by
        show V ⌈(0 : ℝ)⌉₊ 0 = trainDatum c
        rw [Nat.ceil_zero]
        exact (hV 0).initial
      finite_energy := fun s hs => (hV ⌈s⌉₊).finite_energy s ⟨hs, le_ceil_add_one s⟩
      pressure_decay := fun s hs => (hV ⌈s⌉₊).pressure_decay s ⟨hs, le_ceil_add_one s⟩
      stream_differentiable := fun s hs =>
        (hV ⌈s⌉₊).stream_differentiable s ⟨hs, le_ceil_add_one s⟩
      stream := fun s hs => (hV ⌈s⌉₊).stream s ⟨hs, le_ceil_add_one s⟩
      stream_decay := fun s hs => (hV ⌈s⌉₊).stream_decay s ⟨hs, le_ceil_add_one s⟩
      odd := fun s hs => (hV ⌈s⌉₊).odd s ⟨hs, le_ceil_add_one s⟩ }
  show ∃ tr : B0140.TrainSol ν c, IsBUCTrain tr
  refine ⟨⟨glueAge V, glueAge P, glueAge Ψ, hT⟩, ?_⟩
  intro S _ k
  obtain ⟨M, hM⟩ := hB ⌈S⌉₊ k
  refine ⟨M, fun s hs z => ?_⟩
  have hsn : s ≤ (⌈S⌉₊ : ℝ) + 1 := hs.2.trans (le_ceil_add_one S)
  show ‖iteratedFDeriv ℝ k (glueAge V s) z‖ ≤ M
  rw [(hag ⌈S⌉₊ s hs.1 hsn).1]
  exact hM s ⟨hs.1, hsn⟩ z

/-! ### The composition -/

/-- **`TrainGlobalExistence` from the five leaves** (lines 261-288). -/
theorem trainGlobalExistence_of (h1 : MildConcat) (h2 : H3NormOfRep) (h3 : JetL2FromPersistent)
    (h4 : TrainOnUnique) (h5 : ClassicalH3APriori) : TrainGlobalExistence :=
  trainGlobal_of_every h4
    (trainClassicalOnEvery_of (mildTrainGlobal_of h1 (mildTrainH3APriori_of h2 h3 h5)))

end UnforcedLeray.Short.PartI
