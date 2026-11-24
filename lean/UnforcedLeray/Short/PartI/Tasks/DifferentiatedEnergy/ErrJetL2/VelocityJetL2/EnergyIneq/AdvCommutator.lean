import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrJetL2.VelocityJetL2.EnergyIneq.ConsAppend
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ForcingIBP
import UnforcedLeray.Lib.TrainB.SmoothProduct

/-!
# Part I, task `PartI:T08/2/2/2/6/1`: `WordAdvCommutator` (Leibniz for word derivatives)

Target: `theorem wordAdvCommutator_proof : UnforcedLeray.Short.PartI.WordAdvCommutator`.

Source of record: `the November 2 reference manuscript`, lines 352-353; the leaf
statement is in `Sub/PartI_T08_2_2/EnergyIneq.lean`.

Route: the Leibniz rule for a word derivative of a product, written as a sum over the splittings
`wacSplits u` of the word `u` into a part acting on the factor `f` and a part acting on the factor
`g`.  Applied to `scalarAdv b h = ∑_k b_k ∂_k h`, the splitting with all letters on `b` is the
term `b_k ∂_{u ++ [k]} h = b_k ∂_{k :: u} h` (`DerivWordConsAppend`); every other splitting puts
at least one letter on `b`, so it is bounded by `M` times one word of `h` of length `≤ j`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ContDiff Topology

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

/-- Splittings of a word `u` into a pair of subwords `(p.1, p.2)`, the letters of `u` being
distributed between the two factors of a product. -/
def wacSplits : List Bool → List (List Bool × List Bool)
  | [] => [([], [])]
  | b :: u => (wacSplits u).map (fun p => (b :: p.1, p.2)) ++
      (wacSplits u).map (fun p => (p.1, b :: p.2))

theorem wac_splits_length : ∀ u : List Bool, (wacSplits u).length = 2 ^ u.length
  | [] => rfl
  | b :: u => by
    simp only [wacSplits, List.length_append, List.length_map, wac_splits_length u,
      List.length_cons, pow_succ]
    ring

theorem wac_splits_len_sum : ∀ (u : List Bool) (p : List Bool × List Bool),
    p ∈ wacSplits u → p.1.length + p.2.length = u.length
  | [], p, hp => by
    simp only [wacSplits, List.mem_singleton] at hp
    subst hp
    rfl
  | b :: u, p, hp => by
    simp only [wacSplits, List.mem_append, List.mem_map] at hp
    rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · have := wac_splits_len_sum u q hq
      simp only [List.length_cons]
      omega
    · have := wac_splits_len_sum u q hq
      simp only [List.length_cons]
      omega

theorem wac_sum_zero_of {α : Type*} (φ : α → ℝ) :
    ∀ L : List α, (∀ x ∈ L, φ x = 0) → (L.map φ).sum = 0
  | [], _ => rfl
  | x :: L, h => by
    rw [List.map_cons, List.sum_cons, h x (by simp),
      wac_sum_zero_of φ L (fun y hy => h y (by simp [hy]))]
    simp

theorem wac_sum_map_add {α : Type*} (A B : α → ℝ) :
    ∀ L : List α, (L.map (fun p => A p + B p)).sum = (L.map A).sum + (L.map B).sum
  | [] => by simp
  | x :: L => by
    simp only [List.map_cons, List.sum_cons, wac_sum_map_add A B L]
    ring

theorem wac_sum_bound {α : Type*} (φ : α → ℝ) (c : ℝ) (hc : 0 ≤ c) :
    ∀ L : List α, (∀ x ∈ L, |φ x| ≤ c) → |(L.map φ).sum| ≤ (L.length : ℝ) * c
  | [], _ => by simp
  | x :: L, h => by
    have h1 := h x (by simp)
    have h2 := wac_sum_bound φ c hc L (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    calc |φ x + (L.map φ).sum| ≤ |φ x| + |(L.map φ).sum| := abs_add_le _ _
      _ ≤ c + (L.length : ℝ) * c := add_le_add h1 h2
      _ = ((L.length : ℝ) + 1) * c := by ring

theorem wac_split_sum (u : List Bool) (A : List Bool × List Bool → ℝ) :
    ((wacSplits u).map A).sum =
      ((wacSplits u).map (fun p => if p.1 = [] then A p else 0)).sum +
      ((wacSplits u).map (fun p => if p.1 = [] then 0 else A p)).sum := by
  rw [← wac_sum_map_add]
  refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
  by_cases hp : p.1 = [] <;> simp [hp]

/-- Only the splitting with empty first part survives the filter; it is `G u`. -/
theorem wac_filter_sum (G : List Bool → ℝ) : ∀ u : List Bool,
    ((wacSplits u).map (fun p => if p.1 = [] then G p.2 else 0)).sum = G u
  | [] => by simp [wacSplits]
  | b :: u => by
    have hA : (((wacSplits u).map (fun p => (b :: p.1, p.2))).map
        (fun p => if p.1 = [] then G p.2 else 0)).sum = 0 := by
      rw [List.map_map]
      exact wac_sum_zero_of _ _ (fun p _ => by simp)
    have hB : (((wacSplits u).map (fun p => (p.1, b :: p.2))).map
        (fun p => if p.1 = [] then G p.2 else 0)).sum = G (b :: u) := by
      rw [List.map_map]
      have ih : ((wacSplits u).map (fun p => if p.1 = [] then G (b :: p.2) else 0)).sum
          = G (b :: u) := wac_filter_sum (fun v => G (b :: v)) u
      refine Eq.trans (congrArg List.sum (List.map_congr_left fun p _ => ?_)) ih
      simp
    rw [wacSplits, List.map_append, List.sum_append, hA, hB, zero_add]

theorem wac_comp_cd {b : Plane → Vec} (hb : ContDiff ℝ ∞ b) (k : Fin 2) :
    ContDiff ℝ ∞ (fun x => b x k) :=
  (EuclideanSpace.proj k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hb

theorem wac_deriv_cons (a : Bool) (w : List Bool) (f : Plane → ℝ) :
    B0151.derivWord (a :: w) f = B0151.derivWord [a] (B0151.derivWord w f) := by
  cases a <;> rfl

theorem wac_listsum_contDiff {α : Type*} (F : α → Plane → ℝ) :
    ∀ L : List α, (∀ x ∈ L, ContDiff ℝ ∞ (F x)) →
      ContDiff ℝ ∞ (fun z => (L.map (fun x => F x z)).sum)
  | [], _ => by
    simp only [List.map_nil, List.sum_nil]
    exact contDiff_const
  | x :: L, h => by
    simp only [List.map_cons, List.sum_cons]
    exact (h x (by simp)).add (wac_listsum_contDiff F L (fun y hy => h y (by simp [hy])))

theorem wac_listsum_deriv {α : Type*} (F : α → Plane → ℝ) (a : Bool) :
    ∀ L : List α, (∀ x ∈ L, ContDiff ℝ ∞ (F x)) →
      B0151.derivWord [a] (fun z => (L.map (fun x => F x z)).sum) =
        fun z => (L.map (fun x => B0151.derivWord [a] (F x) z)).sum
  | [], _ => by
    funext z
    cases a <;> simp [B0151.derivWord, UnforcedLeray.GaussianVortex.partialX,
      UnforcedLeray.GaussianVortex.partialY]
  | x :: L, h => by
    have hx := h x (by simp)
    have hR := wac_listsum_contDiff F L (fun y hy => h y (by simp [hy]))
    have ih := wac_listsum_deriv F a L (fun y hy => h y (by simp [hy]))
    simp only [List.map_cons, List.sum_cons]
    rw [ForcingIBP.derivWord_add_smooth [a] (F x) _ hx hR, ih]

/-- Leibniz rule for a word derivative of a product, as a sum over `wacSplits u`. -/
theorem wac_leibniz (u : List Bool) : ∀ (f g : Plane → ℝ), ContDiff ℝ ∞ f → ContDiff ℝ ∞ g →
    B0151.derivWord u (fun z => f z * g z) =
      fun z => ((wacSplits u).map
        (fun p => B0151.derivWord p.1 f z * B0151.derivWord p.2 g z)).sum := by
  induction u with
  | nil =>
    intro f g _ _
    funext z
    simp [wacSplits, B0151.derivWord]
  | cons a w ih =>
    intro f g hf hg
    have hw := ih f g hf hg
    rw [wac_deriv_cons a w, hw]
    refine (wac_listsum_deriv (fun p z => B0151.derivWord p.1 f z * B0151.derivWord p.2 g z)
      a (wacSplits w) ?_).trans ?_
    · intro p _
      exact (B0151.contDiff_derivWord hf p.1).mul (B0151.contDiff_derivWord hg p.2)
    · funext z
      have hpt : ∀ p ∈ wacSplits w,
          B0151.derivWord [a] (fun x => B0151.derivWord p.1 f x * B0151.derivWord p.2 g x) z =
            B0151.derivWord (a :: p.1) f z * B0151.derivWord p.2 g z +
              B0151.derivWord p.1 f z * B0151.derivWord (a :: p.2) g z := by
        intro p _
        have hX : ContDiff ℝ ∞ (B0151.derivWord p.1 f) := B0151.contDiff_derivWord hf p.1
        have hY : ContDiff ℝ ∞ (B0151.derivWord p.2 g) := B0151.contDiff_derivWord hg p.2
        rw [TrainB.derivWord_singleton_mul hX hY a, wac_deriv_cons a p.1 f,
          wac_deriv_cons a p.2 g]
      refine (congrArg List.sum (List.map_congr_left hpt)).trans ?_
      refine (wac_sum_map_add _ _ _).trans ?_
      simp only [wacSplits, List.map_append, List.sum_append, List.map_map, Function.comp_def]

/-- The word derivative of `f · ∂_i h`, written as a sum over splittings. -/
theorem wac_gen (u : List Bool) (f h : Plane → ℝ) (hf : ContDiff ℝ ∞ f)
    (hh : ContDiff ℝ ∞ h) (i : Bool) (z : Plane) :
    B0151.derivWord u (fun x => f x * B0151.derivWord [i] h x) z =
      ((wacSplits u).map
        (fun p => B0151.derivWord p.1 f z * B0151.derivWord (p.2 ++ [i]) h z)).sum := by
  rw [wac_leibniz u f _ hf (B0151.contDiff_derivWord hh [i])]
  refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
  rw [vjl_derivWord_append]

theorem wordAdvCommutator_proof : UnforcedLeray.Short.PartI.WordAdvCommutator := by
  intro j
  refine ⟨2 * 2 ^ j, by positivity, ?_⟩
  intro M b h hb hh hbound u hu z
  have hb0 : ContDiff ℝ ∞ (fun x => b x 0) := wac_comp_cd hb 0
  have hb1 : ContDiff ℝ ∞ (fun x => b x 1) := wac_comp_cd hb 1
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hbound [] 0 (Nat.zero_le _) z)
  have hSig0 : 0 ≤ ∑ u' ∈ wordsUpTo j, |B0151.derivWord u' h z| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hX : ContDiff ℝ ∞ (fun x => b x 0 * B0151.derivWord [true] h x) :=
    hb0.mul (B0151.contDiff_derivWord hh [true])
  have hY : ContDiff ℝ ∞ (fun x => b x 1 * B0151.derivWord [false] h x) :=
    hb1.mul (B0151.contDiff_derivWord hh [false])
  have hS : scalarAdv b h = fun x => b x 0 * B0151.derivWord [true] h x +
      b x 1 * B0151.derivWord [false] h x := by
    funext x
    rfl
  have hD : B0151.derivWord u (scalarAdv b h) z =
      B0151.derivWord u (fun x => b x 0 * B0151.derivWord [true] h x) z +
      B0151.derivWord u (fun x => b x 1 * B0151.derivWord [false] h x) z := by
    rw [hS]
    exact congrFun (ForcingIBP.derivWord_add_smooth u _ _ hX hY) z
  have hT : scalarAdv b (B0151.derivWord u h) z =
      b z 0 * B0151.derivWord (true :: u) h z + b z 1 * B0151.derivWord (false :: u) h z := rfl
  have hCA : DerivWordConsAppend := derivWordConsAppend_proof
  have e0 : B0151.derivWord (true :: u) h = B0151.derivWord (u ++ [true]) h :=
    hCA h hh true u
  have e1 : B0151.derivWord (false :: u) h = B0151.derivWord (u ++ [false]) h :=
    hCA h hh false u
  have hT' : scalarAdv b (B0151.derivWord u h) z =
      b z 0 * B0151.derivWord (u ++ [true]) h z + b z 1 * B0151.derivWord (u ++ [false]) h z := by
    rw [hT, e0, e1]
  have G0 : B0151.derivWord u (fun x => b x 0 * B0151.derivWord [true] h x) z =
      ((wacSplits u).map (fun p =>
        B0151.derivWord p.1 (fun x => b x 0) z * B0151.derivWord (p.2 ++ [true]) h z)).sum :=
    wac_gen u (fun x => b x 0) h hb0 hh true z
  have G1 : B0151.derivWord u (fun x => b x 1 * B0151.derivWord [false] h x) z =
      ((wacSplits u).map (fun p =>
        B0151.derivWord p.1 (fun x => b x 1) z * B0151.derivWord (p.2 ++ [false]) h z)).sum :=
    wac_gen u (fun x => b x 1) h hb1 hh false z
  have S0 := wac_split_sum u (fun p =>
    B0151.derivWord p.1 (fun x => b x 0) z * B0151.derivWord (p.2 ++ [true]) h z)
  have S1 := wac_split_sum u (fun p =>
    B0151.derivWord p.1 (fun x => b x 1) z * B0151.derivWord (p.2 ++ [false]) h z)
  have I0 : ((wacSplits u).map (fun p => if p.1 = [] then
      B0151.derivWord p.1 (fun x => b x 0) z * B0151.derivWord (p.2 ++ [true]) h z else 0)).sum
      = b z 0 * B0151.derivWord (u ++ [true]) h z := by
    refine Eq.trans (congrArg List.sum (List.map_congr_left fun p _ => ?_))
      (wac_filter_sum (fun v => b z 0 * B0151.derivWord (v ++ [true]) h z) u)
    by_cases hp : p.1 = [] <;> simp [hp, B0151.derivWord]
  have I1 : ((wacSplits u).map (fun p => if p.1 = [] then
      B0151.derivWord p.1 (fun x => b x 1) z * B0151.derivWord (p.2 ++ [false]) h z else 0)).sum
      = b z 1 * B0151.derivWord (u ++ [false]) h z := by
    refine Eq.trans (congrArg List.sum (List.map_congr_left fun p _ => ?_))
      (wac_filter_sum (fun v => b z 1 * B0151.derivWord (v ++ [false]) h z) u)
    by_cases hp : p.1 = [] <;> simp [hp, B0151.derivWord]
  -- pointwise size of a splitting term with nonempty first part
  have hpiece : ∀ (k : Fin 2) (i : Bool), ∀ p ∈ wacSplits u,
      |(if p.1 = [] then (0 : ℝ) else
        B0151.derivWord p.1 (fun x => b x k) z * B0151.derivWord (p.2 ++ [i]) h z)|
        ≤ M * ∑ u' ∈ wordsUpTo j, |B0151.derivWord u' h z| := by
    intro k i p hp
    split_ifs with hne
    · rw [abs_zero]
      exact mul_nonneg hM0 hSig0
    · have hlen := wac_splits_len_sum u p hp
      have hpos : 0 < p.1.length := by
        cases hq : p.1 with
        | nil => exact absurd hq hne
        | cons x xs => simp
      have h1 : |B0151.derivWord p.1 (fun x => b x k) z| ≤ M := hbound p.1 k (by omega) z
      have h2 : |B0151.derivWord (p.2 ++ [i]) h z| ≤
          ∑ u' ∈ wordsUpTo j, |B0151.derivWord u' h z| := by
        have hmem : p.2 ++ [i] ∈ wordsUpTo j :=
          mem_wordsUpTo.2 (by simp only [List.length_append, List.length_singleton]; omega)
        exact Finset.single_le_sum (f := fun u' => |B0151.derivWord u' h z|)
          (fun _ _ => abs_nonneg _) hmem
      rw [abs_mul]
      exact mul_le_mul h1 h2 (abs_nonneg _) hM0
  have hbnd : ∀ (k : Fin 2) (i : Bool), |((wacSplits u).map (fun p => if p.1 = [] then (0 : ℝ) else
      B0151.derivWord p.1 (fun x => b x k) z * B0151.derivWord (p.2 ++ [i]) h z)).sum|
      ≤ 2 ^ j * (M * ∑ u' ∈ wordsUpTo j, |B0151.derivWord u' h z|) := by
    intro k i
    have hw := wac_sum_bound _ (M * ∑ u' ∈ wordsUpTo j, |B0151.derivWord u' h z|)
      (mul_nonneg hM0 hSig0) (wacSplits u) (fun p hp => hpiece k i p hp)
    rw [wac_splits_length] at hw
    have hp2 : ((2 : ℝ) ^ u.length) ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) hu
    push_cast at hw
    exact hw.trans (mul_le_mul_of_nonneg_right hp2 (mul_nonneg hM0 hSig0))
  obtain ⟨hR0a, hR0b⟩ := abs_le.1 (hbnd 0 true)
  obtain ⟨hR1a, hR1b⟩ := abs_le.1 (hbnd 1 false)
  rw [abs_le]
  constructor
  · linarith
  · linarith

end UnforcedLeray.Short.PartI
