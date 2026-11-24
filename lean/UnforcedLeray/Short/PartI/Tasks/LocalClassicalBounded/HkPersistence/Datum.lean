import UnforcedLeray.Short.PartI.Sub.T02_1_2
import UnforcedLeray.Lib.TrainB.InitialDatumP0H3Fixed
import UnforcedLeray.Units.B0141.Datum

/-!
# Part I, task `PartI:T02/1/2/1`: the projected datum lies in every `H^{k+3}`

Source of record: `the November 2 reference manuscript`, lines 261-288 (the datum
is smooth, periodic, Gaussian, and lies in `H^k` for every `k`).

Target: `projectedDatumPersistent : ProjectedDatumPersistent` (`Sub/T02_1_2.lean`), i.e. for every
`c > 0` and every `k`, some `x : Cyl.H ℝ Cyl.Vec2 c 0 (k + 3)` restricts to
`projectedInitialDatumH3 hc` in `H³`.

Proof.

1. `projectedInitialDatumH3 hc = datumVecH3 hc` (`projectedInitialDatumH3_eq_datumVecH3`): the
   datum components are divergence free, so the cylinder Leray projector fixes them.
2. For every `k`, the element `x_k := Sob.W.ofFields` with fields `hkField c α =
   Sob.iterD ((Sob.cylinder c).word α) (B0140.trainDatum c)`, `α : Sob.Idx 2 (k+3)`. Membership in
   `L²(cell)` of every field comes from `B0141.memHAll_datum` (all jets of the datum lie in
   `L²(cell)`). The weak-derivative identities come from `hasWeakDeriv_cylinder_word_of_smooth_periodic`.
3. Restricting to order `3` keeps the zero-word field, which is the datum. Equality with
   `datumVecH3 hc` is checked by `Sob.W.ext` (values agree almost everywhere).

The order-`n` `L²` bound is a copy of `memLp_datum_word_derivative` (`Lib/TrainB/InitialDatumH3Graph.lean`),
which is stated only for `Sob.Idx 2 3`; the helper declarations there are private, so they are
repeated here under `hk` names.  `Sob.W.ofCylSmooth` is not used (`IsCylSmooth` needs compact
support in `η`, and the datum does not vanish there).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.TrainB

/-! ### The ordered derivative fields of the datum -/

/-- The ordered classical derivative `∂^α (trainDatum c)` for a word `α` of length `≤ n`: the
field of the `H^n` graph of the datum. -/
def hkField (c : ℝ) {n : ℕ} (α : Sob.Idx 2 n) : Plane → Cyl.Vec2 :=
  Sob.iterD ((Sob.cylinder c).word α) (B0140.trainDatum c)

theorem hkField_eq (c : ℝ) {n : ℕ} (α : Sob.Idx 2 n) :
    hkField c α = Sob.iterD ((Sob.cylinder c).word α) (Train.datum c) := by
  unfold hkField
  rw [B0141.trainDatum_eq_datum]

theorem hkField_zero (c : ℝ) {n : ℕ} :
    hkField c (Sob.Idx.zero : Sob.Idx 2 n) = Train.datum c := by
  rw [hkField_eq, Sob.TestDomain.word_zero, Sob.iterD_nil]

/-! ### Measure and `L²` bounds -/

private theorem hkDatum_measure_eq_cell (c : ℝ) :
    Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ)) = Cyl.cellμ c := by
  rw [Cyl.wμ_ρwW c (0 : ℝ), Cyl.wμ]
  simp [Cyl.ρw]

private def hkListDirections (vs : List Plane) : Fin vs.length → Plane := fun i => vs.get i

private theorem hk_norm_cylDir_eq_one (i : Fin 2) : ‖Sob.cylDir i‖ = 1 := by
  fin_cases i <;> simp [Sob.cylDir, Prod.norm_def]

private theorem hk_iterD_eq_iteratedFDeriv_apply (vs : List Plane) (u : Plane → Cyl.Vec2)
    (hu : ContDiff ℝ ∞ u) :
    Sob.iterD vs u = fun z =>
      iteratedFDeriv ℝ vs.length u z (hkListDirections vs) := by
  induction vs with
  | nil =>
      funext z
      simp [Sob.iterD, iteratedFDeriv_zero_apply]
  | cons v vs ih =>
      funext z
      change fderiv ℝ (Sob.iterD vs u) z v =
        iteratedFDeriv ℝ (vs.length + 1) u z (hkListDirections (v :: vs))
      have hm : hkListDirections (v :: vs) = Fin.cons v (hkListDirections vs) := by
        funext i
        refine Fin.cases ?_ ?_ i
        · rfl
        · intro j
          rfl
      rw [hm, iteratedFDeriv_succ_apply_left]
      simp only [Fin.cons_zero, Fin.tail_cons]
      rw [ih]
      have hD : ContDiff ℝ ∞ (iteratedFDeriv ℝ vs.length u) :=
        hu.iteratedFDeriv_right (m := ∞) (i := vs.length)
          UnforcedLeray.Kernels.infty_add_nat_le
      have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ vs.length u) z :=
        (contDiff_iff_contDiffAt.mp hD z).differentiableAt (by simp)
      exact fderiv_continuousMultilinear_apply_const_apply hdiff (hkListDirections vs) v

/-- Every ordered derivative word of the datum lies in `L²(cell)`, for every word length. -/
private theorem hk_memLp_datum_iterD {c : ℝ} (hc : 0 < c) {n : ℕ} (α : Sob.Idx 2 n) :
    MemLp (Sob.iterD ((Sob.cylinder c).word α) (Train.datum c)) 2 (Cyl.cellμ c) := by
  let vs := (Sob.cylinder c).word α
  let k := vs.length
  have hjet : MemLp (Train.jet k (Train.datum c)) 2 (Cyl.cellμ c) :=
    B0141.memHAll_datum hc k
  have hnorm : MemLp (fun z => ‖Train.jet k (Train.datum c) z‖) 2 (Cyl.cellμ c) :=
    hjet.norm
  have hcont : Continuous (Sob.iterD vs (Train.datum c)) :=
    (Sob.contDiff_iterD (Train.datum_contDiff hc.ne') vs).continuous
  apply hnorm.mono' hcont.aestronglyMeasurable
  filter_upwards with z
  rw [hk_iterD_eq_iteratedFDeriv_apply vs (Train.datum c) (Train.datum_contDiff hc.ne')]
  have hbound := (iteratedFDeriv ℝ k (Train.datum c) z).le_opNorm (hkListDirections vs)
  have hprod : ∏ i : Fin k, ‖hkListDirections vs i‖ = 1 := by
    have hword : ∀ v ∈ vs, ‖v‖ = 1 := by
      intro v hv
      have hv' : v ∈ List.ofFn (fun j : Fin α.1.1 => (Sob.cylinder c).dir (α.2 j)) := by
        simpa [vs, Sob.TestDomain.word] using hv
      rcases (List.mem_ofFn' _ _).mp hv' with ⟨i, hi⟩
      rw [← hi]
      exact hk_norm_cylDir_eq_one (α.2 i)
    have heach (i : Fin k) : ‖hkListDirections vs i‖ = 1 :=
      hword (vs.get i) (List.get_mem vs i)
    calc
      ∏ i : Fin k, ‖hkListDirections vs i‖ = ∏ i : Fin k, (1 : ℝ) := by
        apply Finset.prod_congr rfl
        intro i _
        exact heach i
      _ = 1 := by simp
  calc
    ‖iteratedFDeriv ℝ k (Train.datum c) z (hkListDirections vs)‖ ≤
        ‖iteratedFDeriv ℝ k (Train.datum c) z‖ *
          ∏ i : Fin k, ‖hkListDirections vs i‖ := hbound
    _ = ‖Train.jet k (Train.datum c) z‖ := by simp [Train.jet, hprod]

private theorem hk_memLp_hkField {c : ℝ} (hc : 0 < c) {n : ℕ} (α : Sob.Idx 2 n) :
    MemLp (hkField c α) 2 (Cyl.cellμ c) := by
  rw [hkField_eq]
  exact hk_memLp_datum_iterD hc α

/-! ### Weak derivatives -/

private theorem hk_hasWeakDeriv {c : ℝ} (hc : 0 < c) {n : ℕ} (α : Sob.Idx 2 n) :
    Sob.HasWeakDeriv (Sob.cylinder c) ((Sob.cylinder c).word α)
      (hkField c (Sob.Idx.zero : Sob.Idx 2 n)) (hkField c α) := by
  rw [hkField_zero, hkField_eq]
  exact hasWeakDeriv_cylinder_word_of_smooth_periodic hc (Train.datum_contDiff hc.ne')
    (Train.datum_periodic c) ((Sob.cylinder c).word α)

/-! ### The projected datum lies in every `H^{k+3}` -/

/-- **Task `PartI:T02/1/2/1`** (source lines 261-288): for every `c > 0` and every `k`, the
projected datum `projectedInitialDatumH3 hc` is the `H³` restriction of an element of `H^{k+3}`. -/
theorem projectedDatumPersistent : ProjectedDatumPersistent := by
  unfold ProjectedDatumPersistent
  intro c hc k
  have hmem : ∀ α : Sob.Idx 2 (k + 3),
      MemLp (hkField c α) 2 (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) := by
    intro α
    rw [hkDatum_measure_eq_cell c]
    exact hk_memLp_hkField hc α
  refine ⟨Sob.W.ofFields (D := Sob.cylinder c) (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ)
    (F := Cyl.Vec2) (k := k + 3) (p := 2) (fun α => hkField c α) hmem
    (fun α => hk_hasWeakDeriv hc α), ?_⟩
  rw [projectedInitialDatumH3_eq_datumVecH3 hc]
  apply Sob.W.ext
  rw [Sob.W.value_restrict, Sob.W.value_ofFields]
  unfold datumVecH3
  rw [Sob.W.value_ofFields]
  apply Lp.ext
  filter_upwards [(hmem Sob.Idx.zero).coeFn_toLp,
    (datumH3Field_memLp hc Sob.Idx.zero).coeFn_toLp] with z h1 h2
  rw [h1, h2, hkField_zero]
  simp [datumH3Field]

#print axioms UnforcedLeray.Short.PartI.projectedDatumPersistent

end UnforcedLeray.Short.PartI
