import UnforcedLeray.Short.PartI.Sub.T08Statement
import UnforcedLeray.Lib.Cylinder.IBP
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Part I, task `PartI:T08/5`: jet viscous integration by parts

Target: `jetViscousIBP_proof : JetViscousIBP` (`Sub/T08Statement.lean`, leaf 5).

Source of record: `the November 2 reference manuscript` line 348.

Proof outline.
* `derivWord_lap`: word derivatives commute with the scalar Laplacian on smooth fields
  (mixed partials commute by `ContDiffAt.isSymmSndFDerivAt`).
* `word_ibp`: for one smooth periodic `G` with all needed derivatives in `L²(cell)`,
  `∫ G ΔG = -∫ (∂_q G)² - ∫ (∂_η G)²` (`Cyl.integral_cell_partialQ_mul`,
  `Cyl.integral_cell_partialEta_mul`).
* `wordsOfLength_succ_eq`, `sum_wordsOfLength_succ`: reindexing `wordsOfLength (j+1)` as
  `β :: w` with `β` a letter and `w ∈ wordsOfLength j`.
* The main theorem sums the per-word identity over the words of length `j`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)

namespace JetViscIBP

/-! ### Mixed partials of smooth scalar fields -/

theorem cd_partialQ {F : Plane → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (Cyl.partialQ F) := by
  have h : Cyl.partialQ F = fun w => fderiv ℝ F w (1, 0) :=
    funext fun w => Cyl.partialQ_eq_fderiv (hF.differentiable (by simp)) w
  rw [h]
  exact (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem cd_partialEta {F : Plane → ℝ} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (Cyl.partialEta F) := by
  have h : Cyl.partialEta F = fun w => fderiv ℝ F w (0, 1) :=
    funext fun w => Cyl.partialEta_eq_fderiv (hF.differentiable (by simp)) w
  rw [h]
  exact (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem partialQ_fderiv_apply {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) (v z : Plane) :
    Cyl.partialQ (fun x => fderiv ℝ f x v) z = fderiv ℝ (Cyl.partialQ f) z v := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have hfd : ContDiff ℝ 1 (fderiv ℝ f) :=
    hf2.fderiv_right (m := 1) (by norm_num)
  have hdd : Differentiable ℝ (fderiv ℝ f) := hfd.differentiable one_ne_zero
  have hscalar : Differentiable ℝ (fun x => fderiv ℝ f x v) := by
    exact (ContinuousLinearMap.apply ℝ ℝ v).differentiable.comp hdd
  have hq : Cyl.partialQ f = fun x => fderiv ℝ f x (1, 0) := by
    funext x
    exact Cyl.partialQ_eq_fderiv (hf.differentiable (by simp)) x
  rw [Cyl.partialQ_eq_fderiv hscalar z, hq]
  rw [fderiv_clm_apply (hdd z) (differentiableAt_const _),
    fderiv_clm_apply (hdd z) (differentiableAt_const _)]
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)).eq (1, 0) v

/-- Mixed partials commute on smooth scalar fields. -/
theorem comm_QE {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) :
    Cyl.partialQ (Cyl.partialEta f) = Cyl.partialEta (Cyl.partialQ f) := by
  have hQ : ContDiff ℝ ∞ (Cyl.partialQ f) := cd_partialQ hf
  have hdQ : Differentiable ℝ (Cyl.partialQ f) := hQ.differentiable (by simp)
  have hE : Cyl.partialEta f = fun x => fderiv ℝ f x (0, 1) := by
    funext x
    exact Cyl.partialEta_eq_fderiv (hf.differentiable (by simp)) x
  funext z
  rw [hE, partialQ_fderiv_apply hf (0, 1) z, Cyl.partialEta_eq_fderiv hdQ z]

theorem partialQ_add_pt {f g : Plane → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (z : Plane) :
    Cyl.partialQ (fun y => f y + g y) z = Cyl.partialQ f z + Cyl.partialQ g z := by
  have hd : Differentiable ℝ (fun y => f y + g y) := hf.add hg
  rw [Cyl.partialQ_eq_fderiv hd z, Cyl.partialQ_eq_fderiv hf z,
    Cyl.partialQ_eq_fderiv hg z,
    show fderiv ℝ (fun y => f y + g y) z = fderiv ℝ f z + fderiv ℝ g z from fderiv_add (hf z) (hg z)]
  rfl

theorem partialEta_add_pt {f g : Plane → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (z : Plane) :
    Cyl.partialEta (fun y => f y + g y) z = Cyl.partialEta f z + Cyl.partialEta g z := by
  have hd : Differentiable ℝ (fun y => f y + g y) := hf.add hg
  rw [Cyl.partialEta_eq_fderiv hd z, Cyl.partialEta_eq_fderiv hf z,
    Cyl.partialEta_eq_fderiv hg z,
    show fderiv ℝ (fun y => f y + g y) z = fderiv ℝ f z + fderiv ℝ g z from fderiv_add (hf z) (hg z)]
  rfl

/-- `∂_q` commutes with the scalar Laplacian on smooth fields (as functions). -/
theorem partialQ_lap {u : Plane → ℝ} (hu : ContDiff ℝ ∞ u) :
    Cyl.partialQ (fun z => Train.lapS u z) = fun z => Train.lapS (Cyl.partialQ u) z := by
  funext z
  have hA : Differentiable ℝ (Cyl.partialQ (Cyl.partialQ u)) :=
    (cd_partialQ (cd_partialQ hu)).differentiable (by simp)
  have hB : Differentiable ℝ (Cyl.partialEta (Cyl.partialEta u)) :=
    (cd_partialEta (cd_partialEta hu)).differentiable (by simp)
  show Cyl.partialQ (fun y => Cyl.partialQ (Cyl.partialQ u) y + Cyl.partialEta (Cyl.partialEta u) y) z
    = Cyl.partialQ (Cyl.partialQ (Cyl.partialQ u)) z + Cyl.partialEta (Cyl.partialEta (Cyl.partialQ u)) z
  rw [partialQ_add_pt hA hB z]
  rw [comm_QE (cd_partialEta hu), comm_QE hu]

/-- `∂_η` commutes with the scalar Laplacian on smooth fields (as functions). -/
theorem partialEta_lap {u : Plane → ℝ} (hu : ContDiff ℝ ∞ u) :
    Cyl.partialEta (fun z => Train.lapS u z) = fun z => Train.lapS (Cyl.partialEta u) z := by
  funext z
  have hA : Differentiable ℝ (Cyl.partialQ (Cyl.partialQ u)) :=
    (cd_partialQ (cd_partialQ hu)).differentiable (by simp)
  have hB : Differentiable ℝ (Cyl.partialEta (Cyl.partialEta u)) :=
    (cd_partialEta (cd_partialEta hu)).differentiable (by simp)
  show Cyl.partialEta (fun y => Cyl.partialQ (Cyl.partialQ u) y + Cyl.partialEta (Cyl.partialEta u) y) z
    = Cyl.partialQ (Cyl.partialQ (Cyl.partialEta u)) z + Cyl.partialEta (Cyl.partialEta (Cyl.partialEta u)) z
  rw [partialEta_add_pt hA hB z]
  rw [← comm_QE (cd_partialQ hu), ← comm_QE hu]

/-- Word derivatives commute with the scalar Laplacian on smooth fields. -/
theorem derivWord_lap (w : List Bool) :
    ∀ g : Plane → ℝ, ContDiff ℝ ∞ g →
      B0151.derivWord w (fun z => Train.lapS g z) = fun z => Train.lapS (B0151.derivWord w g) z := by
  induction w with
  | nil => intro g _; rfl
  | cons b w ih =>
    intro g hg
    have hw := ih g hg
    cases b with
    | false =>
      show Cyl.partialEta (B0151.derivWord w (fun z => Train.lapS g z))
        = fun z => Train.lapS (Cyl.partialEta (B0151.derivWord w g)) z
      rw [hw]
      exact partialEta_lap (B0151.contDiff_derivWord hg w)
    | true =>
      show Cyl.partialQ (B0151.derivWord w (fun z => Train.lapS g z))
        = fun z => Train.lapS (Cyl.partialQ (B0151.derivWord w g)) z
      rw [hw]
      exact partialQ_lap (B0151.contDiff_derivWord hg w)

/-- Periodicity passes to word derivatives. -/
theorem per_derivWord {c : ℝ} (w : List Bool) :
    ∀ F : Plane → ℝ, Cyl.IsPeriodic c F → Cyl.IsPeriodic c (B0151.derivWord w F) := by
  induction w with
  | nil => intro F hF; exact hF
  | cons b w ih =>
    intro F hF
    cases b with
    | false => exact (ih F hF).partialEta
    | true => exact (ih F hF).partialQ

/-- The vector Laplacian acts componentwise. -/
theorem vecLap_comp (f : Plane → Train.Vec) (k : Fin 2) :
    (fun z => Train.vecLaplacian f z k) = fun z => Train.lapS (fun x => f x k) z := by
  funext z
  fin_cases k
  · simp [Train.vecLaplacian]
  · simp [Train.vecLaplacian]

theorem wordComp_vecLap (f : Plane → Train.Vec) (hf : ContDiff ℝ ∞ f) (w : List Bool) (k : Fin 2) :
    (fun z => wordComp w (Train.vecLaplacian f) k z) = fun z => Train.lapS (wordComp w f k) z := by
  have hk : ContDiff ℝ ∞ (fun x => f x k) :=
    (EuclideanSpace.proj k : Train.Vec →L[ℝ] ℝ).contDiff.comp hf
  unfold wordComp
  rw [vecLap_comp f k]
  exact derivWord_lap w _ hk

/-! ### The scalar integration by parts -/

theorem word_ibp {c : ℝ} (hc : 0 < c) {G : Plane → ℝ} (hG : ContDiff ℝ ∞ G)
    (hp : Cyl.IsPeriodic c G)
    (h0 : MemLp G 2 (Cyl.cellμ c)) (h1 : MemLp (Cyl.partialQ G) 2 (Cyl.cellμ c))
    (h2 : MemLp (Cyl.partialEta G) 2 (Cyl.cellμ c))
    (h11 : MemLp (Cyl.partialQ (Cyl.partialQ G)) 2 (Cyl.cellμ c))
    (h22 : MemLp (Cyl.partialEta (Cyl.partialEta G)) 2 (Cyl.cellμ c)) :
    ∫ z in Cyl.cell c, G z * Train.lapS G z =
      -(∫ z in Cyl.cell c, Cyl.partialQ G z * Cyl.partialQ G z)
        - ∫ z in Cyl.cell c, Cyl.partialEta G z * Cyl.partialEta G z := by
  have dG : Differentiable ℝ G := hG.differentiable (by simp)
  have dQ : Differentiable ℝ (Cyl.partialQ G) := (cd_partialQ hG).differentiable (by simp)
  have dE : Differentiable ℝ (Cyl.partialEta G) := (cd_partialEta hG).differentiable (by simp)
  have iQQG : IntegrableOn (fun z => Cyl.partialQ (Cyl.partialQ G) z * G z) (Cyl.cell c) :=
    h11.integrable_mul h0
  have iQQ : IntegrableOn (fun z => Cyl.partialQ G z * Cyl.partialQ G z) (Cyl.cell c) :=
    h1.integrable_mul h1
  have iEEG : IntegrableOn (fun z => Cyl.partialEta (Cyl.partialEta G) z * G z) (Cyl.cell c) :=
    h22.integrable_mul h0
  have iEG : IntegrableOn (fun z => Cyl.partialEta G z * G z) (Cyl.cell c) :=
    h2.integrable_mul h0
  have iEE : IntegrableOn (fun z => Cyl.partialEta G z * Cyl.partialEta G z) (Cyl.cell c) :=
    h2.integrable_mul h2
  have iQG : IntegrableOn (fun z => Cyl.partialQ G z * G z) (Cyl.cell c) :=
    h1.integrable_mul h0
  have hA : ∫ z in Cyl.cell c, Cyl.partialQ (Cyl.partialQ G) z * G z =
      -∫ z in Cyl.cell c, Cyl.partialQ G z * Cyl.partialQ G z :=
    Cyl.integral_cell_partialQ_mul hc dQ dG hp.partialQ hp iQQG iQQ
  have hB : ∫ z in Cyl.cell c, Cyl.partialEta (Cyl.partialEta G) z * G z =
      -∫ z in Cyl.cell c, Cyl.partialEta G z * Cyl.partialEta G z :=
    Cyl.integral_cell_partialEta_mul dE dG iEG iEEG iEE
  have hsplit : (fun z => G z * Train.lapS G z) =
      fun z => Cyl.partialQ (Cyl.partialQ G) z * G z
        + Cyl.partialEta (Cyl.partialEta G) z * G z := by
    funext z
    unfold Train.lapS
    ring
  rw [hsplit, integral_add iQQG iEEG, hA, hB]
  ring

/-! ### Reindexing words -/

theorem mem_wordsOfLength_iff' {l : ℕ} {w : List Bool} :
    w ∈ wordsOfLength l ↔ w.length = l := by
  unfold wordsOfLength
  constructor
  · intro h
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.1 h
    exact List.length_ofFn
  · intro h
    subst h
    exact Finset.mem_image.2 ⟨w.get, Finset.mem_univ _, List.ofFn_get w⟩

theorem wordsOfLength_succ_eq (j : ℕ) :
    wordsOfLength (j + 1) =
      (Finset.univ ×ˢ wordsOfLength j).image (fun p : Bool × List Bool => p.1 :: p.2) := by
  ext w
  rw [Finset.mem_image, mem_wordsOfLength_iff']
  constructor
  · intro hw
    cases w with
    | nil => simp at hw
    | cons b u =>
      refine ⟨(b, u), ?_, rfl⟩
      rw [Finset.mem_product, mem_wordsOfLength_iff']
      exact ⟨Finset.mem_univ _, by simpa using hw⟩
  · rintro ⟨⟨b, u⟩, hm, rfl⟩
    rw [Finset.mem_product, mem_wordsOfLength_iff'] at hm
    simpa using hm.2

theorem sum_wordsOfLength_succ {M : Type*} [AddCommMonoid M] (j : ℕ) (F : List Bool → M) :
    ∑ w ∈ wordsOfLength (j + 1), F w = ∑ β : Bool, ∑ w ∈ wordsOfLength j, F (β :: w) := by
  rw [wordsOfLength_succ_eq, Finset.sum_image]
  · rw [Finset.sum_product]
  · rintro ⟨a, u⟩ _ ⟨b, v⟩ _ h
    simp only [List.cons.injEq] at h
    exact Prod.ext h.1 h.2

/-- Splitting a sum over words into a sum of integrals. -/
theorem integral_sum_sum {c : ℝ} (s : Finset (List Bool)) (F : List Bool → Fin 2 → Plane → ℝ)
    (hF : ∀ w ∈ s, ∀ k : Fin 2, IntegrableOn (F w k) (Cyl.cell c)) :
    ∫ z in Cyl.cell c, ∑ w ∈ s, ∑ k : Fin 2, F w k z =
      ∑ w ∈ s, ∑ k : Fin 2, ∫ z in Cyl.cell c, F w k z := by
  rw [integral_finset_sum s (fun w hw => integrable_finset_sum _ (fun k _ => hF w hw k))]
  refine Finset.sum_congr rfl fun w hw => ?_
  exact integral_finset_sum _ (fun k _ => hF w hw k)

theorem sum_comm_neg (A : Finset (List Bool)) (T : Bool → List Bool → Fin 2 → ℝ) :
    ∑ w ∈ A, ∑ k : Fin 2, -(∑ β : Bool, T β w k) =
      -(∑ β : Bool, ∑ w ∈ A, ∑ k : Fin 2, T β w k) := by
  have h1 : ∀ w, ∑ k : Fin 2, -(∑ β : Bool, T β w k) =
      -(∑ β : Bool, ∑ k : Fin 2, T β w k) := by
    intro w
    simp only [Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun w _ => h1 w)]
  simp only [Finset.sum_neg_distrib]
  rw [Finset.sum_comm]

end JetViscIBP

open JetViscIBP

/-! ### The main theorem -/

theorem jetViscousIBP_proof : UnforcedLeray.Short.PartI.JetViscousIBP := by
  intro c hc f hf j
  obtain ⟨hsm, hper, hL2⟩ := hf
  have hcomp : ∀ k : Fin 2, ContDiff ℝ ∞ (fun x => f x k) := fun k =>
    (EuclideanSpace.proj k : Train.Vec →L[ℝ] ℝ).contDiff.comp hsm
  have hWs : ∀ (w : List Bool) (k : Fin 2), ContDiff ℝ ∞ (wordComp w f k) := fun w k =>
    B0151.contDiff_derivWord (hcomp k) w
  have hWp : ∀ (w : List Bool) (k : Fin 2), Cyl.IsPeriodic c (wordComp w f k) := by
    intro w k
    refine per_derivWord w (fun x => f x k) ?_
    intro z
    show f (z.1 + c, z.2) k = f z k
    rw [hper z]
  have hLap : ∀ (w : List Bool) (k : Fin 2) (z : Plane),
      wordComp w (Train.vecLaplacian f) k z = Train.lapS (wordComp w f k) z := by
    intro w k z
    exact congrFun (wordComp_vecLap f hsm w k) z
  have hMem : ∀ (w : List Bool) (k : Fin 2),
      MemLp (fun z => Train.lapS (wordComp w f k) z) 2 (Cyl.cellμ c) := by
    intro w k
    exact (hL2 (true :: true :: w) k).add (hL2 (false :: false :: w) k)
  have hI : ∀ (w : List Bool) (k : Fin 2),
      IntegrableOn (fun z => wordComp w f k z * wordComp w (Train.vecLaplacian f) k z) (Cyl.cell c) := by
    intro w k
    simp only [hLap]
    exact (hL2 w k).integrable_mul (hMem w k)
  have hI' : ∀ (w : List Bool) (k : Fin 2),
      IntegrableOn (fun z => wordComp w f k z * wordComp w f k z) (Cyl.cell c) := by
    intro w k
    exact (hL2 w k).integrable_mul (hL2 w k)
  have key : ∀ w ∈ wordsOfLength j, ∀ k : Fin 2,
      ∫ z in Cyl.cell c, wordComp w f k z * wordComp w (Train.vecLaplacian f) k z =
        -∑ β : Bool, ∫ z in Cyl.cell c, wordComp (β :: w) f k z * wordComp (β :: w) f k z := by
    intro w _ k
    simp only [hLap]
    rw [word_ibp hc (hWs w k) (hWp w k) (hL2 w k) (hL2 (true :: w) k) (hL2 (false :: w) k)
      (hL2 (true :: true :: w) k) (hL2 (false :: false :: w) k)]
    rw [Fintype.sum_bool, neg_add]
    rfl
  have hL : jetPair c j f (Train.vecLaplacian f) =
      ∑ w ∈ wordsOfLength j, ∑ k : Fin 2,
        ∫ z in Cyl.cell c, wordComp w f k z * wordComp w (Train.vecLaplacian f) k z := by
    unfold jetPair
    exact integral_sum_sum _ _ (fun w _ k => hI w k)
  have hR : jetEnergy c (j + 1) f =
      ∑ w ∈ wordsOfLength (j + 1), ∑ k : Fin 2,
        ∫ z in Cyl.cell c, wordComp w f k z * wordComp w f k z := by
    unfold jetEnergy jetPair
    exact integral_sum_sum _ _ (fun w _ k => hI' w k)
  have hre : ∑ w ∈ wordsOfLength (j + 1), ∑ k : Fin 2,
      ∫ z in Cyl.cell c, wordComp w f k z * wordComp w f k z =
      ∑ β : Bool, ∑ w ∈ wordsOfLength j, ∑ k : Fin 2,
        ∫ z in Cyl.cell c, wordComp (β :: w) f k z * wordComp (β :: w) f k z :=
    sum_wordsOfLength_succ j (fun w => ∑ k : Fin 2,
      ∫ z in Cyl.cell c, wordComp w f k z * wordComp w f k z)
  rw [hL, hR, hre]
  rw [Finset.sum_congr rfl fun w hw => Finset.sum_congr rfl fun k _ => key w hw k]
  exact sum_comm_neg _ (fun β w k => ∫ z in Cyl.cell c, wordComp (β :: w) f k z * wordComp (β :: w) f k z)
