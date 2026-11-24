import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2_2_1_2_1_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GELinSub.rawSmoothBdd_Sub.Sub.RingLiftOffAxis_Sub.HeatFieldJet

/-!
# `PartIII-b:C/ward/12/3/2/2/1/2/1/2/4`: `MeanBlockB2LateHeatSplit2`

Source of record: `the November 2 reference manuscript`, lines 447-459
(`sct:expansion`), 1256 (`B₂ = -v₁(K+1)H + H H_η + 2ν(K+1)H_q - ν(K+1)²v₂`), 1267-1268
(`K ∂_η^j G_{νs} = -(j+1) ∂_η^j G_{νs}`), 1281-1283, 1310-1325, 2548-2551.

This file proves the late-age finite-order heat decomposition for the quadratic axial mean block
`ringEps p.R ^ 2 * Jet.B2.meanB2 p.ν p.c p.train` along `meridE1`:
- `meanBlockB2LateHeatSplit2_at (N : ℕ)`: unconditional fixed-order `N` late heat decomposition
  (with `∀ N : ℕ` outside `∃ ν₀ : ℝ`, matching `LateMeanRemainder` and `TrainMeanExpansion`, and
  sufficient for `resNearAxisJet2_of` at `N = K + 1`);
- `meanBlockB2LateHeatSplit2_of`: `MeanBlockB2LateHeatSplit2` from uniform-`ν₀` remainder words.
-/

set_option autoImplicit false

noncomputable section

open UnforcedLeray.PhaseSpace MeasureTheory Set Filter Topology
open scoped ContDiff BigOperators
open UnforcedLeray.Cons.C03.Concrete (Params)
open UnforcedLeray.B0184 UnforcedLeray.B0185 UnforcedLeray.B0187 UnforcedLeray.B0188
  UnforcedLeray.B0190 UnforcedLeray.Short.PartIIa
open UnforcedLeray.Short.PartI

namespace UnforcedLeray.Short.PartIIIb.Concrete

open FarDecaySub EarlyJet2Sub LateHeatDecomp2Sub

namespace BlockB2Sub

/-! ### 1. Translation invariance along `eqDir` (`q`-independence) -/

/-- A profile on `ProfilePoint` is `q`-invariant if translating along `eqDir = (1, (0, 0))`
leaves it unchanged everywhere. -/
def QInv (g : ProfilePoint → ℝ) : Prop :=
  ∀ x : ProfilePoint, ∀ t : ℝ, g (x + t • eqDir) = g x

theorem QInv.fderiv_eq {g : ProfilePoint → ℝ} (hg : QInv g) (x : ProfilePoint) (t : ℝ) :
    fderiv ℝ g (x + t • eqDir) = fderiv ℝ g x := by
  have hcomp : (fun y : ProfilePoint => g (y + t • eqDir)) = g :=
    funext fun y => hg y t
  have h := fderiv_comp_add_right (𝕜 := ℝ) (f := g) (x := x) (t • eqDir)
  change fderiv ℝ (fun y : ProfilePoint => g (y + t • eqDir)) x = fderiv ℝ g (x + t • eqDir) at h
  rw [hcomp] at h
  exact h.symm

theorem QInv.const (c : ℝ) : QInv (fun _ => c) := fun _ _ => rfl

theorem QInv.add {f g : ProfilePoint → ℝ} (hf : QInv f) (hg : QInv g) :
    QInv (fun x => f x + g x) := fun x t => by simp [hf x t, hg x t]

theorem QInv.sub {f g : ProfilePoint → ℝ} (hf : QInv f) (hg : QInv g) :
    QInv (fun x => f x - g x) := fun x t => by simp [hf x t, hg x t]

theorem QInv.neg {f : ProfilePoint → ℝ} (hf : QInv f) :
    QInv (fun x => -f x) := fun x t => by simp [hf x t]

theorem QInv.mul {f g : ProfilePoint → ℝ} (hf : QInv f) (hg : QInv g) :
    QInv (fun x => f x * g x) := fun x t => by simp [hf x t, hg x t]

theorem QInv.const_mul (c : ℝ) {f : ProfilePoint → ℝ} (hf : QInv f) :
    QInv (fun x => c * f x) := fun x t => by simp [hf x t]

theorem QInv.sum {ι : Type*} (s : Finset ι) {f : ι → ProfilePoint → ℝ}
    (hf : ∀ i ∈ s, QInv (f i)) : QInv (fun x => ∑ i ∈ s, f i x) :=
  fun x t => Finset.sum_congr rfl fun i hi => hf i hi x t

theorem QInv.partialEta {f : ProfilePoint → ℝ} (hf : QInv f) : QInv (partialEta f) :=
  fun x t => by simp only [UnforcedLeray.B0184.partialEta, hf.fderiv_eq x t]

theorem QInv.partialAge {f : ProfilePoint → ℝ} (hf : QInv f) : QInv (partialAge f) :=
  fun x t => by simp only [UnforcedLeray.B0184.partialAge, hf.fderiv_eq x t]

theorem QInv.ageOperator {f : ProfilePoint → ℝ} (hf : QInv f) : QInv (ageOperator f) := by
  intro x t
  have h2 : (x + t • eqDir).2 = x.2 := by simp [eqDir]
  simp only [UnforcedLeray.B0184.ageOperator, h2, hf.partialEta x t, hf.partialAge x t]

theorem QInv.ageShift (k : ℝ) {f : ProfilePoint → ℝ} (hf : QInv f) : QInv (ageShift k f) :=
  hf.ageOperator.add (hf.const_mul k)

theorem QInv.partialQ_eq_zero {f : ProfilePoint → ℝ} (hf : QInv f)
    (hsm : ContDiffOn ℝ ∞ f ageDomain) {x : ProfilePoint} (hx : x ∈ ageDomain) :
    partialQ f x = 0 := by
  have hd : DifferentiableAt ℝ f x :=
    (hsm.contDiffAt (FarDecaySub.isOpen_ageDomain.mem_nhds hx)).differentiableAt (by simp)
  exact Jet.B2.remQ_fderiv_zero hd (hf x)

theorem qInv_meanFam (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) :
    QInv (Jet.meanFam ν c tr) := by
  intro x t
  have h2 : (x + t • eqDir).2 = x.2 := by simp [eqDir]
  show meanStream tr (x + t • eqDir).2.2 (x + t • eqDir).2.1 = meanStream tr x.2.2 x.2.1
  rw [h2]

theorem qInv_lhP (ν : ℝ) (m : ℕ) : QInv (lhP ν m) := by
  intro x t
  have h2 : (x + t • eqDir).2 = x.2 := by simp [eqDir]
  show UnforcedLeray.B0191.heatDeriv ν m (x + t • eqDir).2.1 (x + t • eqDir).2.2 =
    UnforcedLeray.B0191.heatDeriv ν m x.2.1 x.2.2
  rw [h2]

/-! ### 2. Order-`N` heat sum `S_heat N` and mean remainder `remFamN N` -/

/-- The order-`N` mean remainder profile family `R_N(q, η, s) = meanRemainder tr N s η`. -/
def remFamN (N : ℕ) : Jet.Fam :=
  fun _ _ tr => trainProfile fun s z => meanRemainder tr N s z.2

/-- The order-`N` finite heat expansion profile family `∑_{j ≤ N} a_{2j} ∂_η^{2j} G_{νs}(η)`. -/
def S_heat (N : ℕ) : Jet.Fam :=
  fun ν _ tr x => ∑ j ∈ Finset.range (N + 1), meanCoeff tr j * lhP ν (2 * j) x

theorem qInv_remFamN (N : ℕ) (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) :
    QInv (remFamN N ν c tr) := by
  intro x t
  have h2 : (x + t • eqDir).2 = x.2 := by simp [eqDir]
  show meanRemainder tr N (x + t • eqDir).2.2 (x + t • eqDir).2.1 =
    meanRemainder tr N x.2.2 x.2.1
  rw [h2]

theorem qInv_S_heat (N : ℕ) (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) :
    QInv (S_heat N ν c tr) :=
  QInv.sum (Finset.range (N + 1)) fun j _ => (qInv_lhP ν (2 * j)).const_mul (meanCoeff tr j)

theorem meanFam_eq_S_heat_add_remFamN (N : ℕ) :
    Jet.meanFam = S_heat N + remFamN N := by
  funext ν c tr x
  show trainProfile (fun s z => meanStream tr s z.2) x =
    (∑ j ∈ Finset.range (N + 1), meanCoeff tr j * lhP ν (2 * j) x) +
      trainProfile (fun s z => meanRemainder tr N s z.2) x
  simp only [trainProfile, meanRemainder, lhP_eq]
  ring

theorem contDiffOn_lhP {ν : ℝ} (hν : 0 < ν) (m : ℕ) :
    ContDiffOn ℝ ∞ (lhP ν m) ageDomain := by
  have hH : ContDiffOn ℝ ∞ (heatProfile ν) ageDomain :=
    (Jet.heatWords_of LateHeatDecomp2Sub.lateIngredients.heat Jet.jetToolkit.iterLin ν hν).1
  exact (contDiffOn_partialEta_iter hH m).congr
    fun y hy => (lhIter ν m y hy).symm

theorem S_heat_smooth (N : ℕ) : Jet.JSmooth (S_heat N) := by
  intro ν c hν _ tr _
  exact ContDiffOn.sum fun j _ => contDiffOn_const.mul (contDiffOn_lhP hν (2 * j))

theorem remFamN_smooth (N : ℕ) : Jet.JSmooth (remFamN N) := by
  intro ν c hν hc tr htr
  have hM : ContDiffOn ℝ ∞ (Jet.meanFam ν c tr) ageDomain :=
    LateHeatDecomp2Sub.meanWords_uncond.1 ν c hν hc tr htr
  have hS : ContDiffOn ℝ ∞ (S_heat N ν c tr) ageDomain :=
    S_heat_smooth N ν c hν hc tr htr
  have heq : remFamN N ν c tr = fun x => Jet.meanFam ν c tr x - S_heat N ν c tr x := by
    funext x
    have h := congr_fun (congr_fun (congr_fun (congr_fun (meanFam_eq_S_heat_add_remFamN N) ν) c) tr) x
    change Jet.meanFam ν c tr x = S_heat N ν c tr x + remFamN N ν c tr x at h
    linarith
  rw [heq]
  exact hM.sub hS

theorem remFamN_words (N : ℕ) : Jet.WordsW ((N : ℝ) + 3 / 2) (remFamN N) := by
  have hJ := remFamN_smooth N
  refine ⟨hJ, ?_, ?_⟩
  · intro ν c hν hc tr htr x hx
    exact (qInv_remFamN N ν c tr).partialQ_eq_zero (hJ ν c hν hc tr htr) hx
  · intro ℓ b ρ m hρ
    obtain ⟨C, M, ν₀, hν₀, H⟩ := LateHeatDecomp2Sub.lateIngredients.remainder ρ N m b ℓ hρ
    refine ⟨C, M, ν₀, hν₀, fun ν hν hle tr htr x hx => ?_⟩
    have hb := H ν hν hle tr htr x hx
    have e : -(((N : ℝ) + 3 / 2) + (b : ℝ) / 2) = -(((b : ℝ) + 2 * (N : ℝ) + 3) / 2) := by ring
    show (1 + x.2.1 ^ 2 / x.2.2) ^ m *
        |(ageOperator^[ℓ] (partialEta^[b] (trainProfile fun s z => meanRemainder tr N s z.2))) x| ≤
      polyConst C M ν (ν ^ (-ρ)) * x.2.2 ^ (-(((N : ℝ) + 3 / 2) + (b : ℝ) / 2))
    rw [e]
    exact hb

theorem remFamN_JQ (N n : ℕ) : Jet.JQ n ((N : ℝ) + 3 / 2) (remFamN N) :=
  Jet.JQ_of_words Jet.jetToolkit.jc Jet.jetToolkit.wordW n _ _ (remFamN_words N)

theorem meanFam_JQ (n : ℕ) : Jet.JQ n (1 / 2) Jet.meanFam :=
  Jet.JQ_of_words Jet.jetToolkit.jc Jet.jetToolkit.wordW n _ _ LateHeatDecomp2Sub.meanWords_uncond

theorem S_heat_JQ (N n : ℕ) : Jet.JQ n (1 / 2) (S_heat N) := by
  have heq : S_heat N = Jet.meanFam - remFamN N := by
    rw [meanFam_eq_S_heat_add_remFamN N, add_sub_cancel_right]
  rw [heq]
  exact Jet.jetToolkit.jc.qsub (meanFam_JQ n)
    (Jet.jetToolkit.jc.qmono (by linarith : (1 / 2 : ℝ) ≤ (N : ℝ) + 3 / 2) (remFamN_JQ N n))

/-! ### 3. Bilinear form `b2Form` and remainder `remB2 N` -/

/-- `-∂_η F`. -/
def v1Op (F : Jet.Fam) : Jet.Fam := -Jet.famEta F

/-- `(1 - K) F`. -/
def hOp (F : Jet.Fam) : Jet.Fam := F - Jet.famK F

/-- Bilinear form of Block `B₂`: `b2Form F G = -(v1Op F * (K+1)(hOp G)) + hOp F * ∂_η(hOp G)`. -/
def b2Form (F G : Jet.Fam) : Jet.Fam :=
  -(v1Op F * Jet.famShift 1 (hOp G)) + hOp F * Jet.famEta (hOp G)

/-- Remainder family of `Jet.B2.meanB2` at expansion order `N`. -/
def remB2 (N : ℕ) : Jet.Fam :=
  b2Form (S_heat N) (remFamN N) + b2Form (remFamN N) Jet.meanFam

theorem qInv_b2Form {F G : Jet.Fam} (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c)
    (hF : QInv (F ν c tr)) (hG : QInv (G ν c tr)) :
    QInv (b2Form F G ν c tr) := by
  have hv1 : QInv (v1Op F ν c tr) := hF.partialEta.neg
  have hhF : QInv (hOp F ν c tr) := hF.sub hF.ageOperator
  have hhG : QInv (hOp G ν c tr) := hG.sub hG.ageOperator
  exact (hv1.mul (hhG.ageShift 1)).neg.add (hhF.mul hhG.partialEta)

theorem qInv_remB2 (N : ℕ) (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c) :
    QInv (remB2 N ν c tr) :=
  (qInv_b2Form ν c tr (qInv_S_heat N ν c tr) (qInv_remFamN N ν c tr)).add
    (qInv_b2Form ν c tr (qInv_remFamN N ν c tr) (qInv_meanFam ν c tr))

theorem v1Op_JQ {a : ℝ} {F : Jet.Fam} (hF : ∀ n, Jet.JQ n a F) (n : ℕ) :
    Jet.JQ n (a + 1 / 2) (v1Op F) :=
  Jet.jetToolkit.jc.qneg (hF (n + 1)).eta

theorem hOp_JQ {a : ℝ} {F : Jet.Fam} (hF : ∀ n, Jet.JQ n a F) (n : ℕ) :
    Jet.JQ n a (hOp F) :=
  Jet.jetToolkit.jc.qsub (hF n) (hF (n + 1)).k

theorem b2Form_JQ {a b : ℝ} {F G : Jet.Fam} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hF : ∀ n, Jet.JQ n a F) (hG : ∀ n, Jet.JQ n b G) (n : ℕ) :
    Jet.JQ n (a + b + 1 / 2) (b2Form F G) := by
  have h1 : Jet.JQ n (a + 1 / 2 + b) (v1Op F * Jet.famShift 1 (hOp G)) :=
    Jet.jetToolkit.jc.qmul (by linarith) hb (v1Op_JQ hF n)
      (Jet.jetToolkit.jc.qshift 1 (hOp_JQ hG (n + 1)))
  have h1' : Jet.JQ n (a + b + 1 / 2) (-(v1Op F * Jet.famShift 1 (hOp G))) :=
    Jet.jetToolkit.jc.qneg (h1.cast (by ring))
  have h2 : Jet.JQ n (a + (b + 1 / 2)) (hOp F * Jet.famEta (hOp G)) :=
    Jet.jetToolkit.jc.qmul ha (by linarith) (hOp_JQ hF n) (hOp_JQ hG (n + 1)).eta
  exact Jet.jetToolkit.jc.qadd h1' (h2.cast (by ring))

theorem remB2_JQ (N n : ℕ) : Jet.JQ n (N : ℝ) (remB2 N) := by
  have h1 : Jet.JQ n (1 / 2 + ((N : ℝ) + 3 / 2) + 1 / 2) (b2Form (S_heat N) (remFamN N)) :=
    b2Form_JQ (by norm_num) (by positivity) (S_heat_JQ N) (remFamN_JQ N) n
  have h2 : Jet.JQ n (((N : ℝ) + 3 / 2) + 1 / 2 + 1 / 2) (b2Form (remFamN N) Jet.meanFam) :=
    b2Form_JQ (by positivity) (by norm_num) (remFamN_JQ N) meanFam_JQ n
  have hsum : Jet.JQ n ((N : ℝ) + 5 / 2) (remB2 N) :=
    Jet.jetToolkit.jc.qadd (h1.cast (by ring)) (h2.cast (by ring))
  exact Jet.jetToolkit.jc.qmono (by linarith) hsum

theorem v1Op_add {A B : Jet.Fam} (hA : Jet.JSmooth A) (hB : Jet.JSmooth B) :
    Jet.LateEq (v1Op (A + B)) (v1Op A + v1Op B) := by
  have heta := (Jet.jetToolkit.linOps A B hA hB 0).2.1
  intro ν c hν hc tr htr x hx
  have e := heta ν c hν hc tr htr hx
  show -partialEta (A ν c tr + B ν c tr) x = -partialEta (A ν c tr) x + -partialEta (B ν c tr) x
  change partialEta (A ν c tr + B ν c tr) x = partialEta (A ν c tr) x + partialEta (B ν c tr) x at e
  linarith

theorem hOp_add {A B : Jet.Fam} (hA : Jet.JSmooth A) (hB : Jet.JSmooth B) :
    Jet.LateEq (hOp (A + B)) (hOp A + hOp B) := by
  have hk := (Jet.jetToolkit.linOps A B hA hB 0).1
  intro ν c hν hc tr htr x hx
  have e := hk ν c hν hc tr htr hx
  show (A ν c tr x + B ν c tr x) - ageOperator (A ν c tr + B ν c tr) x =
    (A ν c tr x - ageOperator (A ν c tr) x) + (B ν c tr x - ageOperator (B ν c tr) x)
  change ageOperator (A ν c tr + B ν c tr) x = ageOperator (A ν c tr) x + ageOperator (B ν c tr) x at e
  linarith

theorem hOp_smooth {A : Jet.Fam} (hA : Jet.JSmooth A) : Jet.JSmooth (hOp A) :=
  fun ν c hν hc tr htr =>
    (hA ν c hν hc tr htr).sub ((Jet.jetToolkit.smooth A A hA hA).2.2.2.2.1 ν c hν hc tr htr)

/-- Pointwise late decomposition of `Jet.B2.meanB2` on `ageDomain` into the bilinear heat-sum
part `b2Form (S_heat N) (S_heat N)` and `remB2 N`. -/
theorem meanB2_decomp_late (N : ℕ) :
    Jet.LateEq Jet.B2.meanB2 (b2Form (S_heat N) (S_heat N) + remB2 N) := by
  set A := S_heat N
  set B := remFamN N
  have hA : Jet.JSmooth A := S_heat_smooth N
  have hB : Jet.JSmooth B := remFamN_smooth N
  have hhA : Jet.JSmooth (hOp A) := hOp_smooth hA
  have hhB : Jet.JSmooth (hOp B) := hOp_smooth hB
  have hv1 := v1Op_add hA hB
  have hh := hOp_add hA hB
  have hsh := (Jet.B2.shift_congr Jet.jetToolkit hh 1).trans
    (Jet.B2.shift_add Jet.jetToolkit hhA hhB 1)
  have heta := (Jet.jetToolkit.eqOps _ _ hh).2.1.trans
    (Jet.jetToolkit.linOps (hOp A) (hOp B) hhA hhB 0).2.1
  intro ν c hν hc tr htr x hx
  have hM_eq : Jet.meanFam = A + B := meanFam_eq_S_heat_add_remFamN N
  have ev1 : v1Op Jet.meanFam ν c tr x = v1Op A ν c tr x + v1Op B ν c tr x := by
    rw [hM_eq]; exact hv1 ν c hν hc tr htr hx
  have eh : hOp Jet.meanFam ν c tr x = hOp A ν c tr x + hOp B ν c tr x := by
    rw [hM_eq]; exact hh ν c hν hc tr htr hx
  have esh : Jet.famShift 1 (hOp Jet.meanFam) ν c tr x =
      Jet.famShift 1 (hOp A) ν c tr x + Jet.famShift 1 (hOp B) ν c tr x := by
    rw [hM_eq]; exact hsh ν c hν hc tr htr hx
  have eeta : Jet.famEta (hOp Jet.meanFam) ν c tr x =
      Jet.famEta (hOp A) ν c tr x + Jet.famEta (hOp B) ν c tr x := by
    rw [hM_eq]; exact heta ν c hν hc tr htr hx
  show -(v1Op Jet.meanFam ν c tr x * Jet.famShift 1 (hOp Jet.meanFam) ν c tr x) +
      hOp Jet.meanFam ν c tr x * Jet.famEta (hOp Jet.meanFam) ν c tr x =
    (-(v1Op A ν c tr x * Jet.famShift 1 (hOp A) ν c tr x) +
      hOp A ν c tr x * Jet.famEta (hOp A) ν c tr x) +
    ((-(v1Op A ν c tr x * Jet.famShift 1 (hOp B) ν c tr x) +
      hOp A ν c tr x * Jet.famEta (hOp B) ν c tr x) +
     (-(v1Op B ν c tr x * Jet.famShift 1 (hOp Jet.meanFam) ν c tr x) +
      hOp B ν c tr x * Jet.famEta (hOp Jet.meanFam) ν c tr x))
  linear_combination
    -(Jet.famShift 1 (hOp Jet.meanFam) ν c tr x) * ev1 -
      (v1Op A ν c tr x) * esh +
      (Jet.famEta (hOp Jet.meanFam) ν c tr x) * eh +
      (hOp A ν c tr x) * eeta

/-! ### 4. Explicit heat-kernel evaluation of `b2Form (S_heat N) (S_heat N)` -/

/-- Linear combination of even heat profile derivatives `∑_{j < M} c_j ∂_η^{2j} G_{νs}(η)`. -/
def lhLinComb (ν : ℝ) (M : ℕ) (c : ℕ → ℝ) (y : ProfilePoint) : ℝ :=
  ∑ j ∈ Finset.range M, c j * lhP ν (2 * j) y

theorem partialEta_sum {ι : Type*} (s : Finset ι) (f : ι → ProfilePoint → ℝ) {x : ProfilePoint}
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) x) :
    partialEta (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, partialEta (f i) x := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp [partialEta]
  | @insert a s ha ih =>
    have hfa : DifferentiableAt ℝ (f a) x := hf a (Finset.mem_insert_self a s)
    have hfs : DifferentiableAt ℝ (fun y => ∑ i ∈ s, f i y) x :=
      DifferentiableAt.fun_sum fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hfd : fderiv ℝ (fun y => f a y + ∑ i ∈ s, f i y) x =
        fderiv ℝ (f a) x + fderiv ℝ (fun y => ∑ i ∈ s, f i y) x :=
      (hfa.hasFDerivAt.add hfs.hasFDerivAt).fderiv
    simp only [Finset.sum_insert ha]
    change (fderiv ℝ (fun y => f a y + ∑ i ∈ s, f i y) x) eηDir =
      partialEta (f a) x + ∑ i ∈ s, partialEta (f i) x
    rw [hfd, add_apply, ← ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]
    rfl

theorem ageOperator_sum {ι : Type*} (s : Finset ι) (f : ι → ProfilePoint → ℝ) {x : ProfilePoint}
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) x) :
    ageOperator (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, ageOperator (f i) x := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp [ageOperator, partialEta, partialAge]
  | @insert a s ha ih =>
    have hfa : DifferentiableAt ℝ (f a) x := hf a (Finset.mem_insert_self a s)
    have hfs : DifferentiableAt ℝ (fun y => ∑ i ∈ s, f i y) x :=
      DifferentiableAt.fun_sum fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hfd : fderiv ℝ (fun y => f a y + ∑ i ∈ s, f i y) x =
        fderiv ℝ (f a) x + fderiv ℝ (fun y => ∑ i ∈ s, f i y) x :=
      (hfa.hasFDerivAt.add hfs.hasFDerivAt).fderiv
    simp only [Finset.sum_insert ha]
    have hadd : ageOperator (fun y => f a y + ∑ i ∈ s, f i y) x =
        ageOperator (f a) x + ageOperator (fun y => ∑ i ∈ s, f i y) x := by
      unfold ageOperator partialEta partialAge
      rw [hfd, add_apply, add_apply]
      ring
    rw [hadd, ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

theorem partialEta_lhLinComb (ν : ℝ) (M : ℕ) (c : ℕ → ℝ) {x : ProfilePoint} (hx : 0 < x.2.2) :
    partialEta (lhLinComb ν M c) x = ∑ j ∈ Finset.range M, c j * lhP ν (2 * j + 1) x := by
  unfold lhLinComb
  rw [partialEta_sum (Finset.range M) (fun j y => c j * lhP ν (2 * j) y)
    (fun j _ => (lhDiff ν (2 * j) hx).const_mul (c j))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [bB2_partialEta_const_mul (lhDiff ν (2 * j) hx) (c j), lhPartialEta ν (2 * j) hx]

theorem ageOperator_lhLinComb (ν : ℝ) (M : ℕ) (c : ℕ → ℝ) {x : ProfilePoint} (hx : 0 < x.2.2) :
    ageOperator (lhLinComb ν M c) x =
      ∑ j ∈ Finset.range M, (-(2 * (j : ℝ) + 1) * c j) * lhP ν (2 * j) x := by
  unfold lhLinComb
  rw [ageOperator_sum (Finset.range M) (fun j y => c j * lhP ν (2 * j) y)
    (fun j _ => (lhDiff ν (2 * j) hx).const_mul (c j))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [bB2_ageOperator_const_mul (lhDiff ν (2 * j) hx) (c j), bB2_K_lhP ν (2 * j) hx]
  push_cast
  ring

theorem hOp_S_heat_eq (N : ℕ) (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c)
    {x : ProfilePoint} (hx : 0 < x.2.2) :
    hOp (S_heat N) ν c tr x =
      lhLinComb ν (N + 1) (fun j => (2 * (j : ℝ) + 2) * meanCoeff tr j) x := by
  have hS : S_heat N ν c tr = lhLinComb ν (N + 1) (meanCoeff tr) := rfl
  show S_heat N ν c tr x - ageOperator (S_heat N ν c tr) x = _
  rw [hS, ageOperator_lhLinComb ν (N + 1) (meanCoeff tr) hx]
  unfold lhLinComb
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem b2Form_S_heat_eq (N : ℕ) (ν c : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c)
    {x : ProfilePoint} (hx : 0 < x.2.2) :
    b2Form (S_heat N) (S_heat N) ν c tr x =
      ∑ j₁ ∈ Finset.range (N + 1), ∑ j₂ ∈ Finset.range (N + 1),
        ((-(2 * (j₂ : ℝ)) * (2 * (j₂ : ℝ) + 2) * meanCoeff tr j₁ * meanCoeff tr j₂) *
          (lhP ν (2 * j₂) x * lhP ν (2 * j₁ + 1) x) +
         ((2 * (j₁ : ℝ) + 2) * (2 * (j₂ : ℝ) + 2) * meanCoeff tr j₁ * meanCoeff tr j₂) *
          (lhP ν (2 * j₁) x * lhP ν (2 * j₂ + 1) x)) := by
  set c' : ℕ → ℝ := fun j => (2 * (j : ℝ) + 2) * meanCoeff tr j
  have hev : hOp (S_heat N) ν c tr =ᶠ[𝓝 x] lhLinComb ν (N + 1) c' :=
    Filter.eventuallyEq_of_mem (lhMemNhds hx) (fun y hy => hOp_S_heat_eq N ν c tr hy)
  have hh_val : hOp (S_heat N) ν c tr x = lhLinComb ν (N + 1) c' x := hev.eq_of_nhds
  have hh_eta : Jet.famEta (hOp (S_heat N)) ν c tr x =
      ∑ j₂ ∈ Finset.range (N + 1), c' j₂ * lhP ν (2 * j₂ + 1) x := by
    show partialEta (hOp (S_heat N) ν c tr) x = _
    unfold partialEta
    rw [hev.fderiv_eq]
    exact partialEta_lhLinComb ν (N + 1) c' hx
  have hh_sh : Jet.famShift 1 (hOp (S_heat N)) ν c tr x =
      ∑ j₂ ∈ Finset.range (N + 1), (-(2 * (j₂ : ℝ)) * c' j₂) * lhP ν (2 * j₂) x := by
    show ageOperator (hOp (S_heat N) ν c tr) x + 1 * hOp (S_heat N) ν c tr x = _
    rw [bB2_ageOperator_congr hev, hh_val, ageOperator_lhLinComb ν (N + 1) c' hx]
    unfold lhLinComb
    rw [ one_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j₂ _ => ?_
    ring
  have hv1 : v1Op (S_heat N) ν c tr x =
      ∑ j₁ ∈ Finset.range (N + 1), (-meanCoeff tr j₁) * lhP ν (2 * j₁ + 1) x := by
    show -partialEta (lhLinComb ν (N + 1) (meanCoeff tr)) x = _
    rw [partialEta_lhLinComb ν (N + 1) (meanCoeff tr) hx, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j₁ _ => ?_
    ring
  show -(v1Op (S_heat N) ν c tr x * Jet.famShift 1 (hOp (S_heat N)) ν c tr x) +
      hOp (S_heat N) ν c tr x * Jet.famEta (hOp (S_heat N)) ν c tr x = _
  rw [hv1, hh_sh, hh_val, hh_eta]
  unfold lhLinComb
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j₁ _ => ?_
  rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j₂ _ => ?_
  dsimp [c']
  ring

/-! ### 5. Smooth Cartesian lift of `lhP ν (2a) * lhP ν (2b+1)` along `meridE1` -/

/-- Cartesian lift of `coeff * ∂_η^{2a} G_{νs}(η) * ∂_η^{2b+1} G_{νs}(η) • meridE1` under
`Axi.age R z • Axi.Nv R · τ z`:
`(coeff * R^{-2(a+b)} * (z₀² + z₁²)^{a+b} * G_ν^{(2a)}(z₂) * G_ν^{(2b+1)}(z₂)) • e₃`. -/
def heatPairTermE1 (ν R coeff : ℝ) (a b : ℕ) (z : UnforcedLeray.Space) : UnforcedLeray.Space :=
  (coeff * R⁻¹ ^ (2 * (a + b)) * (z 0 ^ 2 + z 1 ^ 2) ^ (a + b) *
    UnforcedLeray.B0191.profileDeriv ν (2 * a) (z 2) *
    UnforcedLeray.B0191.profileDeriv ν (2 * b + 1) (z 2)) • Axi.e3

theorem lhP_chartSwap_chart (ν : ℝ) {R : ℝ} (hR : 0 < R) (τ : ℝ)
    {z : UnforcedLeray.Space} (hz : z ∉ Axi.axis) (m : ℕ) :
    lhP ν m (chartSwap (Axi.chart R τ z)) =
      (Axi.ϱ z / R) ^ (m + 1) * UnforcedLeray.B0191.profileDeriv ν m (z 2) := by
  have hϱ : 0 < Axi.ϱ z := Axi.ϱ_pos hz
  have hlam : 0 < R / Axi.ϱ z := div_pos hR hϱ
  have hhom := UnforcedLeray.B0191.heatDeriv_homogeneous ν m (z 2) one_pos hlam
  have htrans : (chartSwap (Axi.chart R τ z)).2.1 = R / Axi.ϱ z * z 2 := by
    show Axi.trans R z = R / Axi.ϱ z * z 2
    unfold Axi.trans
    ring
  have hage : (chartSwap (Axi.chart R τ z)).2.2 = (R / Axi.ϱ z) ^ 2 * 1 := by
    show Axi.age R z = (R / Axi.ϱ z) ^ 2 * 1
    unfold Axi.age
    ring
  unfold lhP
  rw [htrans, hage, hhom, inv_div]
  rfl

theorem frameL_meridE1 (z : UnforcedLeray.Space) :
    Axi.frameL z LateHeatDecomp2Sub.meridE1 = Axi.e3 := by
  simp [Axi.frameL_apply, LateHeatDecomp2Sub.meridE1]

theorem age_mul_sqrt_age {R : ℝ} (hR : 0 < R) {z : UnforcedLeray.Space} (hz : z ∉ Axi.axis) :
    Axi.age R z * Real.sqrt (Axi.age R z) = (R / Axi.ϱ z) ^ 3 := by
  have hϱ : 0 < Axi.ϱ z := Axi.ϱ_pos hz
  have hlam : 0 < R / Axi.ϱ z := div_pos hR hϱ
  have hage : Axi.age R z = (R / Axi.ϱ z) ^ 2 := by
    unfold Axi.age
    ring
  rw [hage, Real.sqrt_sq hlam.le]
  ring

/-- Off the axis (`z ∉ Axi.axis`) and for `R > 0`, `heatPairTermE1 ν R coeff a b z` agrees
pointwise with `Axi.age R z • Axi.Nv R (fun m => (coeff * (lhP ν (2a) * lhP ν (2b+1))) • meridE1) τ z`. -/
theorem heatPairTermE1_eq_age_smul_Nv (ν : ℝ) {R : ℝ} (hR : 0 < R) (coeff : ℝ) (a b : ℕ)
    (τ : ℝ) {z : UnforcedLeray.Space} (hz : z ∉ Axi.axis) :
    Axi.age R z • Axi.Nv R
      (fun m => (coeff * (lhP ν (2 * a) (chartSwap m) * lhP ν (2 * b + 1) (chartSwap m))) •
        LateHeatDecomp2Sub.meridE1) τ z =
      heatPairTermE1 ν R coeff a b z := by
  have hϱ : 0 < Axi.ϱ z := Axi.ϱ_pos hz
  have hϱ0 : Axi.ϱ z ≠ 0 := hϱ.ne'
  have hR0 : R ≠ 0 := hR.ne'
  rw [UnforcedLeray.Short.IIb.ChartJetsAux.Nv_eq_fun]
  dsimp only
  rw [map_smul, frameL_meridE1, smul_smul, smul_smul, age_mul_sqrt_age hR hz,
    lhP_chartSwap_chart ν hR τ hz (2 * a), lhP_chartSwap_chart ν hR τ hz (2 * b + 1)]
  unfold heatPairTermE1
  congr 1
  rw [← Axi.ϱ_sq z]
  have hpow1 : (Axi.ϱ z / R) ^ (2 * a + 1) = Axi.ϱ z * (Axi.ϱ z ^ 2) ^ a * R⁻¹ ^ (2 * a + 1) := by
    rw [div_eq_mul_inv, mul_pow]
    ring
  have hpow2 : (Axi.ϱ z / R) ^ (2 * b + 1 + 1) =
      Axi.ϱ z ^ 2 * (Axi.ϱ z ^ 2) ^ b * R⁻¹ ^ (2 * b + 2) := by
    rw [div_eq_mul_inv, mul_pow]
    ring
  have hpowR : R⁻¹ ^ (2 * (a + b)) = R ^ 3 * R⁻¹ ^ (2 * a + 1) * R⁻¹ ^ (2 * b + 2) := by
    have hR_inv : R * R⁻¹ = 1 := mul_inv_cancel₀ hR0
    calc R⁻¹ ^ (2 * (a + b))
        = (R * R⁻¹) ^ 3 * R⁻¹ ^ (2 * (a + b)) := by rw [hR_inv, one_pow, one_mul]
      _ = R ^ 3 * R⁻¹ ^ (2 * a + 1) * R⁻¹ ^ (2 * b + 2) := by ring
  rw [hpow1, hpow2, hpowR, pow_add (Axi.ϱ z ^ 2) a b]
  field_simp

theorem contDiff_heatPairTermE1 (ν R coeff : ℝ) (a b : ℕ) :
    ContDiff ℝ ∞ (heatPairTermE1 ν R coeff a b) := by
  unfold heatPairTermE1
  have c2 : ContDiff ℝ ∞ (fun z : UnforcedLeray.Space => z 2) := by fun_prop
  have c_rad : ContDiff ℝ ∞
      (fun z : UnforcedLeray.Space => coeff * R⁻¹ ^ (2 * (a + b)) * (z 0 ^ 2 + z 1 ^ 2) ^ (a + b)) := by
    fun_prop
  have cg1 : ContDiff ℝ ∞
      (fun z : UnforcedLeray.Space => UnforcedLeray.B0191.profileDeriv ν (2 * a) (z 2)) :=
    (UnforcedLeray.Short.IIb.contDiff_profileDeriv ν (2 * a)).comp c2
  have cg2 : ContDiff ℝ ∞
      (fun z : UnforcedLeray.Space => UnforcedLeray.B0191.profileDeriv ν (2 * b + 1) (z 2)) :=
    (UnforcedLeray.Short.IIb.contDiff_profileDeriv ν (2 * b + 1)).comp c2
  exact ((c_rad.mul cg1).mul cg2).smul contDiff_const

/-! ### 6. Weighted `(1 + y₂²)` second-jet bound for `heatPairTermE1` on `ϱ(y) ≤ R` -/

theorem profileDeriv_eq_iteratedDeriv_heatKernel1 (ν : ℝ) (m : ℕ) (z : ℝ) :
    UnforcedLeray.B0191.profileDeriv ν m z = iteratedDeriv m (heatKernel1 ν) z := by
  have h1 := lhHeatKernelEq ν m z 1
  unfold UnforcedLeray.B0191.profileDeriv UnforcedLeray.B0191.profile
  simpa [UnforcedLeray.B0191.heatDeriv] using h1

/-- For any `ν > 0` and `m : ℕ`, `(1 + z²) |G_ν^{(m)}(z)|` is globally bounded on `z ∈ ℝ`. -/
theorem profileDeriv_wtd1_bdd {ν : ℝ} (hν : 0 < ν) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, (1 + z ^ 2) * |UnforcedLeray.B0191.profileDeriv ν m z| ≤ C := by
  obtain ⟨Q, hQ⟩ := lhPoly m
  obtain ⟨B, hB0, hB⟩ := lhPolyGauss Q 1
  set K : ℝ := (Real.sqrt (4 * Real.pi * ν))⁻¹ * (Real.sqrt ν)⁻¹ ^ m * max 1 ν
  have hK0 : 0 ≤ K := by
    unfold K
    positivity
  refine ⟨K * B, mul_nonneg hK0 hB0, fun z => ?_⟩
  rw [profileDeriv_eq_iteratedDeriv_heatKernel1, hQ ν hν z]
  set u : ℝ := z / Real.sqrt ν
  have hu2 : z ^ 2 = ν * u ^ 2 := by
    dsimp [u]
    rw [div_pow, Real.sq_sqrt hν.le]
    field_simp
  have h1z : 1 + z ^ 2 ≤ max 1 ν * (1 + u ^ 2) := by
    have h1 : (1 : ℝ) ≤ max 1 ν := le_max_left 1 ν
    have h2 : ν ≤ max 1 ν := le_max_right 1 ν
    rw [hu2]
    nlinarith [sq_nonneg u]
  have hexp_eq : -(z ^ 2) / (4 * ν) = -(u ^ 2 / 4) := by
    rw [hu2]
    have hν0 : ν ≠ 0 := hν.ne'
    field_simp
  have habs :
      |(Real.sqrt (4 * Real.pi * ν))⁻¹ * (Real.sqrt ν)⁻¹ ^ m * Q.eval u *
          Real.exp (-(z ^ 2) / (4 * ν))| =
        (Real.sqrt (4 * Real.pi * ν))⁻¹ * (Real.sqrt ν)⁻¹ ^ m * |Q.eval u| *
          Real.exp (-(u ^ 2 / 4)) := by
    rw [hexp_eq, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg (by positivity : 0 ≤ (Real.sqrt (4 * Real.pi * ν))⁻¹),
      abs_of_nonneg (by positivity : 0 ≤ (Real.sqrt ν)⁻¹ ^ m),
      abs_of_pos (Real.exp_pos _)]
  rw [habs]
  have hbu := hB u
  simp only [pow_one] at hbu
  calc (1 + z ^ 2) *
        ((Real.sqrt (4 * Real.pi * ν))⁻¹ * (Real.sqrt ν)⁻¹ ^ m * |Q.eval u| *
          Real.exp (-(u ^ 2 / 4)))
      ≤ (max 1 ν * (1 + u ^ 2)) *
          ((Real.sqrt (4 * Real.pi * ν))⁻¹ * (Real.sqrt ν)⁻¹ ^ m * |Q.eval u| *
            Real.exp (-(u ^ 2 / 4))) :=
        mul_le_mul_of_nonneg_right h1z (by positivity)
    _ = K * ((1 + u ^ 2) * |Q.eval u| * Real.exp (-(u ^ 2 / 4))) := by
        unfold K; ring
    _ ≤ K * B := mul_le_mul_of_nonneg_left hbu hK0

theorem hfjProfileDeriv_wtd1 {ν : ℝ} (hν : 0 < ν) (m k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : UnforcedLeray.Space,
      (1 + y 2 ^ 2) *
        ‖iteratedFDeriv ℝ k (fun w : UnforcedLeray.Space =>
          UnforcedLeray.B0191.profileDeriv ν m (w 2)) y‖ ≤ C := by
  obtain ⟨C, hC0, hC⟩ := profileDeriv_wtd1_bdd hν (m + k)
  set P : UnforcedLeray.Space →L[ℝ] ℝ := EuclideanSpace.proj (2 : Fin 3)
  have hg : ContDiff ℝ ∞ (UnforcedLeray.B0191.profileDeriv ν m) :=
    UnforcedLeray.Short.IIb.contDiff_profileDeriv ν m
  have hfun : (fun w : UnforcedLeray.Space => UnforcedLeray.B0191.profileDeriv ν m (w 2)) =
      UnforcedLeray.B0191.profileDeriv ν m ∘ P := rfl
  refine ⟨C * ‖P‖ ^ k, mul_nonneg hC0 (pow_nonneg (norm_nonneg _) _), fun y => ?_⟩
  rw [hfun, ContinuousLinearMap.iteratedFDeriv_comp_right P hg y (by exact_mod_cast le_top)]
  have hcomp := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ k (UnforcedLeray.B0191.profileDeriv ν m) (P y)) (fun _ => P)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hcomp
  have h1d : ‖iteratedFDeriv ℝ k (UnforcedLeray.B0191.profileDeriv ν m) (P y)‖ =
      |UnforcedLeray.B0191.profileDeriv ν (m + k) (y 2)| := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hfjProfileDerivEq ν k m, Real.norm_eq_abs]
    rfl
  rw [h1d] at hcomp
  have hW0 : 0 ≤ 1 + y 2 ^ 2 := by positivity
  calc (1 + y 2 ^ 2) *
        ‖(iteratedFDeriv ℝ k (UnforcedLeray.B0191.profileDeriv ν m) (P y)).compContinuousLinearMap
          fun _ => P‖
      ≤ (1 + y 2 ^ 2) * (|UnforcedLeray.B0191.profileDeriv ν (m + k) (y 2)| * ‖P‖ ^ k) :=
        mul_le_mul_of_nonneg_left hcomp hW0
    _ = ((1 + y 2 ^ 2) * |UnforcedLeray.B0191.profileDeriv ν (m + k) (y 2)|) * ‖P‖ ^ k := by ring
    _ ≤ C * ‖P‖ ^ k := mul_le_mul_of_nonneg_right (hC (y 2)) (pow_nonneg (norm_nonneg _) _)

/-- Weighted second-jet bound on `Axi.ϱ y ≤ R` for each `heatPairTermE1`. -/
theorem heatPairTermE1_wtd_jet2_bdd {ν : ℝ} (hν : 0 < ν) (R coeff : ℝ) (a b : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : UnforcedLeray.Space, Axi.ϱ y ≤ R →
      (1 + y 2 ^ 2) * ‖iteratedFDeriv ℝ 2 (heatPairTermE1 ν R coeff a b) y‖ ≤ C := by
  set W : ℝ := R ^ 2
  let f : UnforcedLeray.Space → ℝ := fun z =>
    (coeff * R⁻¹ ^ (2 * (a + b))) * ((z 0 ^ 2 + z 1 ^ 2) ^ (a + b) *
      UnforcedLeray.B0191.profileDeriv ν (2 * a) (z 2))
  let g : UnforcedLeray.Space → ℝ := fun z =>
    UnforcedLeray.B0191.profileDeriv ν (2 * b + 1) (z 2)
  have c0 : ContDiff ℝ ∞ (fun y : UnforcedLeray.Space => y 0) := by fun_prop
  have c1 : ContDiff ℝ ∞ (fun y : UnforcedLeray.Space => y 1) := by fun_prop
  have c2 : ContDiff ℝ ∞ (fun y : UnforcedLeray.Space => y 2) := by fun_prop
  have cw : ContDiff ℝ ∞ (fun y : UnforcedLeray.Space => y 0 ^ 2 + y 1 ^ 2) := by fun_prop
  have cf : ContDiff ℝ ∞ f := by
    dsimp [f]
    exact contDiff_const.mul ((cw.pow (a + b)).mul
      ((UnforcedLeray.Short.IIb.contDiff_profileDeriv ν (2 * a)).comp c2))
  have cg : ContDiff ℝ ∞ g :=
    (UnforcedLeray.Short.IIb.contDiff_profileDeriv ν (2 * b + 1)).comp c2
  have h0 : HeatJetBdd W (fun y : UnforcedLeray.Space => y 0) :=
    hfjCoord (W := W) 0 (fun y => le_add_of_nonneg_right (sq_nonneg _))
  have h1 : HeatJetBdd W (fun y : UnforcedLeray.Space => y 1) :=
    hfjCoord (W := W) 1 (fun y => le_add_of_nonneg_left (sq_nonneg _))
  have hw : HeatJetBdd W (fun y : UnforcedLeray.Space => y 0 ^ 2 + y 1 ^ 2) :=
    hfjAdd (f := fun y : UnforcedLeray.Space => y 0 ^ 2)
      (g := fun y : UnforcedLeray.Space => y 1 ^ 2)
      (by fun_prop) (by fun_prop) (hfjPow c0 h0 2) (hfjPow c1 h1 2)
  have hP : HeatJetBdd W (fun y : UnforcedLeray.Space => (y 0 ^ 2 + y 1 ^ 2) ^ (a + b)) :=
    hfjPow cw hw (a + b)
  have hGa : HeatJetBdd W
      (fun y : UnforcedLeray.Space => UnforcedLeray.B0191.profileDeriv ν (2 * a) (y 2)) :=
    hfjCompProj (W := W) (UnforcedLeray.Short.IIb.contDiff_profileDeriv ν (2 * a))
      (fun k' => hfjProfileDeriv hν (2 * a) k') 2
  have Hf : HeatJetBdd W f :=
    hfjMul contDiff_const ((cw.pow (a + b)).mul
      ((UnforcedLeray.Short.IIb.contDiff_profileDeriv ν (2 * a)).comp c2))
      (hfjConst _) (hfjMul (cw.pow (a + b))
        ((UnforcedLeray.Short.IIb.contDiff_profileDeriv ν (2 * a)).comp c2) hP hGa)
  choose Cf hCf0 hCf using Hf
  choose Cg hCg0 hCg using fun k => hfjProfileDeriv_wtd1 hν (2 * b + 1) k
  set L : ℝ →L[ℝ] UnforcedLeray.Space := (ContinuousLinearMap.id ℝ ℝ).smulRight Axi.e3
  set M : ℝ := ∑ i ∈ Finset.range 3, ((2 : ℕ).choose i : ℝ) * Cf i * Cg (2 - i)
  have hM0 : 0 ≤ M :=
    Finset.sum_nonneg fun i _ =>
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCf0 i)) (hCg0 (2 - i))
  refine ⟨‖L‖ * M, mul_nonneg (norm_nonneg _) hM0, fun y hy => ?_⟩
  have hyW : Axi.ϱ y ^ 2 ≤ W := pow_le_pow_left₀ (Axi.ϱ_nonneg y) hy 2
  have hfun : heatPairTermE1 ν R coeff a b = L ∘ (fun z => f z * g z) := by
    funext z
    simp [heatPairTermE1, L, f, g, mul_assoc]
  have hfg_at : ContDiffAt ℝ ∞ (fun z => f z * g z) y := (cf.mul cg).contDiffAt
  have hL_le : ‖iteratedFDeriv ℝ 2 (heatPairTermE1 ν R coeff a b) y‖ ≤
      ‖L‖ * ‖iteratedFDeriv ℝ 2 (fun z => f z * g z) y‖ := by
    rw [hfun]
    exact L.norm_iteratedFDeriv_comp_left hfg_at (by decide : ((2 : ℕ) : ℕ∞ω) ≤ ∞)
  have hmul_le :=
    norm_iteratedFDeriv_mul_le cf cg y (n := 2) (by decide : ((2 : ℕ) : ℕ∞ω) ≤ ∞)
  have hW0 : 0 ≤ 1 + y 2 ^ 2 := by positivity
  have hW_fg : (1 + y 2 ^ 2) * ‖iteratedFDeriv ℝ 2 (fun z => f z * g z) y‖ ≤ M := by
    calc (1 + y 2 ^ 2) * ‖iteratedFDeriv ℝ 2 (fun z => f z * g z) y‖
        ≤ (1 + y 2 ^ 2) * ∑ i ∈ Finset.range 3,
            ((2 : ℕ).choose i : ℝ) * ‖iteratedFDeriv ℝ i f y‖ *
              ‖iteratedFDeriv ℝ (2 - i) g y‖ :=
          mul_le_mul_of_nonneg_left hmul_le hW0
      _ = ∑ i ∈ Finset.range 3,
            ((2 : ℕ).choose i : ℝ) * ‖iteratedFDeriv ℝ i f y‖ *
              ((1 + y 2 ^ 2) * ‖iteratedFDeriv ℝ (2 - i) g y‖) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
      _ ≤ M := by
          refine Finset.sum_le_sum fun i _ => ?_
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left (hCf i y hyW) (Nat.cast_nonneg _))
            (hCg (2 - i) y) (by positivity)
            (mul_nonneg (Nat.cast_nonneg _) (hCf0 i))
  calc (1 + y 2 ^ 2) * ‖iteratedFDeriv ℝ 2 (heatPairTermE1 ν R coeff a b) y‖
      ≤ (1 + y 2 ^ 2) * (‖L‖ * ‖iteratedFDeriv ℝ 2 (fun z => f z * g z) y‖) :=
        mul_le_mul_of_nonneg_left hL_le hW0
    _ = ‖L‖ * ((1 + y 2 ^ 2) * ‖iteratedFDeriv ℝ 2 (fun z => f z * g z) y‖) := by ring
    _ ≤ ‖L‖ * M := mul_le_mul_of_nonneg_left hW_fg (norm_nonneg _)

theorem wtd_jet2_add {F G : UnforcedLeray.Space → UnforcedLeray.Space} {R : ℝ}
    (hsmF : ContDiff ℝ ∞ F) (hsmG : ContDiff ℝ ∞ G)
    (hbdF : ∃ C : ℝ, 0 ≤ C ∧ ∀ y : UnforcedLeray.Space, Axi.ϱ y ≤ R →
      (1 + y 2 ^ 2) * ‖iteratedFDeriv ℝ 2 F y‖ ≤ C)
    (hbdG : ∃ C : ℝ, 0 ≤ C ∧ ∀ y : UnforcedLeray.Space, Axi.ϱ y ≤ R →
      (1 + y 2 ^ 2) * ‖iteratedFDeriv ℝ 2 G y‖ ≤ C) :
    ContDiff ℝ ∞ (fun y => F y + G y) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ y : UnforcedLeray.Space, Axi.ϱ y ≤ R →
        (1 + y 2 ^ 2) * ‖iteratedFDeriv ℝ 2 (fun z => F z + G z) y‖ ≤ C := by
  obtain ⟨CF, hCF0, hCF⟩ := hbdF
  obtain ⟨CG, hCG0, hCG⟩ := hbdG
  refine ⟨hsmF.add hsmG, CF + CG, add_nonneg hCF0 hCG0, fun y hy => ?_⟩
  have cF : ContDiffAt ℝ 2 F y := hsmF.contDiffAt.of_le (by norm_num)
  have cG : ContDiffAt ℝ 2 G y := hsmG.contDiffAt.of_le (by norm_num)
  have hadd : iteratedFDeriv ℝ 2 (fun z => F z + G z) y =
      iteratedFDeriv ℝ 2 F y + iteratedFDeriv ℝ 2 G y :=
    iteratedFDeriv_add_apply cF cG
  rw [hadd]
  have hW0 : 0 ≤ 1 + y 2 ^ 2 := by positivity
  have hnorm := mul_le_mul_of_nonneg_left
    (norm_add_le (iteratedFDeriv ℝ 2 F y) (iteratedFDeriv ℝ 2 G y)) hW0
  linarith [hCF y hy, hCG y hy]

/-- Finite sum of `C^∞` vector fields on `Space` with `(1 + y₂²) ‖D² F_i(y)‖ ≤ C_i` on `ϱ(y) ≤ R`
satisfies the same bound with the summed constant. -/
theorem wtd_jet2_sum {ι : Type*} (s : Finset ι) (F : ι → UnforcedLeray.Space → UnforcedLeray.Space)
    (R : ℝ) (hsm : ∀ i ∈ s, ContDiff ℝ ∞ (F i))
    (hbd : ∀ i ∈ s, ∃ C : ℝ, 0 ≤ C ∧ ∀ y : UnforcedLeray.Space, Axi.ϱ y ≤ R →
      (1 + y 2 ^ 2) * ‖iteratedFDeriv ℝ 2 (F i) y‖ ≤ C) :
    ContDiff ℝ ∞ (fun y => ∑ i ∈ s, F i y) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ y : UnforcedLeray.Space, Axi.ϱ y ≤ R →
        (1 + y 2 ^ 2) * ‖iteratedFDeriv ℝ 2 (fun z => ∑ i ∈ s, F i z) y‖ ≤ C := by
  classical
  induction s using Finset.induction with
  | empty =>
    refine ⟨contDiff_const, 0, le_rfl, fun y _ => ?_⟩
    simp only [Finset.sum_empty]
    rw [iteratedFDeriv_const_of_ne (by decide : (2 : ℕ) ≠ 0) 0]
    simp
  | @insert a s ha ih =>
    have hsm_a : ContDiff ℝ ∞ (F a) := hsm a (Finset.mem_insert_self a s)
    have hbd_a := hbd a (Finset.mem_insert_self a s)
    obtain ⟨hsm_s, hbd_s⟩ := ih
      (fun i hi => hsm i (Finset.mem_insert_of_mem hi))
      (fun i hi => hbd i (Finset.mem_insert_of_mem hi))
    have hfun : (fun z => ∑ i ∈ insert a s, F i z) = fun z => F a z + ∑ i ∈ s, F i z :=
      funext fun z => Finset.sum_insert ha
    rw [hfun]
    exact wtd_jet2_add hsm_a hsm_s hbd_a hbd_s

/-- The explicit Cartesian heat field `F_heat_B2 p N` for Block `B₂` at expansion order `N`. -/
def F_heat_B2 (p : Params) (N : ℕ) (z : UnforcedLeray.Space) : UnforcedLeray.Space :=
  ∑ j₁ ∈ Finset.range (N + 1), ∑ j₂ ∈ Finset.range (N + 1),
    (heatPairTermE1 p.ν p.R
      (ringEps p.R ^ 2 * (-(2 * (j₂ : ℝ)) * (2 * (j₂ : ℝ) + 2) *
        meanCoeff p.train j₁ * meanCoeff p.train j₂)) j₂ j₁ z +
     heatPairTermE1 p.ν p.R
      (ringEps p.R ^ 2 * ((2 * (j₁ : ℝ) + 2) * (2 * (j₂ : ℝ) + 2) *
        meanCoeff p.train j₁ * meanCoeff p.train j₂)) j₁ j₂ z)

theorem F_heat_B2_smooth_and_jet2 (p : Params) (N : ℕ) :
    ContDiff ℝ ∞ (F_heat_B2 p N) ∧
      ∃ C_heat : ℝ, 0 ≤ C_heat ∧ ∀ y : UnforcedLeray.Space, Axi.ϱ y ≤ p.R →
        (1 + y 2 ^ 2) * ‖iteratedFDeriv ℝ 2 (F_heat_B2 p N) y‖ ≤ C_heat := by
  have hinner : ∀ j₁ : ℕ,
      ContDiff ℝ ∞ (fun z => ∑ j₂ ∈ Finset.range (N + 1),
        (heatPairTermE1 p.ν p.R
          (ringEps p.R ^ 2 * (-(2 * (j₂ : ℝ)) * (2 * (j₂ : ℝ) + 2) *
            meanCoeff p.train j₁ * meanCoeff p.train j₂)) j₂ j₁ z +
         heatPairTermE1 p.ν p.R
          (ringEps p.R ^ 2 * ((2 * (j₁ : ℝ) + 2) * (2 * (j₂ : ℝ) + 2) *
            meanCoeff p.train j₁ * meanCoeff p.train j₂)) j₁ j₂ z)) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ y : UnforcedLeray.Space, Axi.ϱ y ≤ p.R →
        (1 + y 2 ^ 2) * ‖iteratedFDeriv ℝ 2 (fun z => ∑ j₂ ∈ Finset.range (N + 1),
          (heatPairTermE1 p.ν p.R
            (ringEps p.R ^ 2 * (-(2 * (j₂ : ℝ)) * (2 * (j₂ : ℝ) + 2) *
              meanCoeff p.train j₁ * meanCoeff p.train j₂)) j₂ j₁ z +
           heatPairTermE1 p.ν p.R
            (ringEps p.R ^ 2 * ((2 * (j₁ : ℝ) + 2) * (2 * (j₂ : ℝ) + 2) *
              meanCoeff p.train j₁ * meanCoeff p.train j₂)) j₁ j₂ z)) y‖ ≤ C := by
    intro j₁
    exact wtd_jet2_sum (Finset.range (N + 1)) _ p.R
      (fun j₂ _ => (wtd_jet2_add (contDiff_heatPairTermE1 _ _ _ _ _)
        (contDiff_heatPairTermE1 _ _ _ _ _)
        (heatPairTermE1_wtd_jet2_bdd p.ν_pos p.R _ j₂ j₁)
        (heatPairTermE1_wtd_jet2_bdd p.ν_pos p.R _ j₁ j₂)).1)
      (fun j₂ _ => (wtd_jet2_add (contDiff_heatPairTermE1 _ _ _ _ _)
        (contDiff_heatPairTermE1 _ _ _ _ _)
        (heatPairTermE1_wtd_jet2_bdd p.ν_pos p.R _ j₂ j₁)
        (heatPairTermE1_wtd_jet2_bdd p.ν_pos p.R _ j₁ j₂)).2)
  unfold F_heat_B2
  exact wtd_jet2_sum (Finset.range (N + 1)) _ p.R
    (fun j₁ _ => (hinner j₁).1) (fun j₁ _ => (hinner j₁).2)

/-- Off the axis (`z ∉ Axi.axis`), the lifted `B₂` mean profile decomposes into `F_heat_B2 p N z`
plus the lift of `ringEps p.R ^ 2 * remB2 N p.ν p.c p.train`. -/
theorem meanB2_lift_decomp (p : Params) (htr : IsBUCTrain p.train) (hR : 2 ≤ p.R) (N : ℕ)
    (τ : ℝ) {z : UnforcedLeray.Space} (hz : z ∉ Axi.axis) :
    Axi.age p.R z • Axi.Nv p.R
      (fun m => (ringEps p.R ^ 2 * Jet.B2.meanB2 p.ν p.c p.train (chartSwap m)) •
        LateHeatDecomp2Sub.meridE1) τ z =
      F_heat_B2 p N z +
        Axi.age p.R z • Axi.Nv p.R
          (fun m => (ringEps p.R ^ 2 * remB2 N p.ν p.c p.train (chartSwap m)) •
            LateHeatDecomp2Sub.meridE1) τ z := by
  have hR0 : 0 < p.R := by linarith
  have hϱ : 0 < Axi.ϱ z := Axi.ϱ_pos hz
  set x : ProfilePoint := chartSwap (Axi.chart p.R τ z)
  have hx : 0 < x.2.2 := by
    show 0 < Axi.age p.R z
    unfold Axi.age
    exact div_pos (pow_pos hR0 2) (pow_pos hϱ 2)
  have hsplit := meanB2_decomp_late N p.ν p.c p.ν_pos p.c_pos p.train htr hx
  change Jet.B2.meanB2 p.ν p.c p.train x =
    b2Form (S_heat N) (S_heat N) p.ν p.c p.train x + remB2 N p.ν p.c p.train x at hsplit
  have hheat := b2Form_S_heat_eq N p.ν p.c p.train hx
  have hF_eq : F_heat_B2 p N z =
      Axi.age p.R z • (Real.sqrt (Axi.age p.R z) •
        ((ringEps p.R ^ 2 * b2Form (S_heat N) (S_heat N) p.ν p.c p.train x) •
          Axi.frameL z LateHeatDecomp2Sub.meridE1)) := by
    unfold F_heat_B2
    have hterms : ∀ j₁ ∈ Finset.range (N + 1), ∀ j₂ ∈ Finset.range (N + 1),
        heatPairTermE1 p.ν p.R
          (ringEps p.R ^ 2 * (-(2 * (j₂ : ℝ)) * (2 * (j₂ : ℝ) + 2) *
            meanCoeff p.train j₁ * meanCoeff p.train j₂)) j₂ j₁ z +
        heatPairTermE1 p.ν p.R
          (ringEps p.R ^ 2 * ((2 * (j₁ : ℝ) + 2) * (2 * (j₂ : ℝ) + 2) *
            meanCoeff p.train j₁ * meanCoeff p.train j₂)) j₁ j₂ z =
        (Axi.age p.R z * Real.sqrt (Axi.age p.R z) * ringEps p.R ^ 2 *
          ((-(2 * (j₂ : ℝ)) * (2 * (j₂ : ℝ) + 2) * meanCoeff p.train j₁ * meanCoeff p.train j₂) *
            (lhP p.ν (2 * j₂) x * lhP p.ν (2 * j₁ + 1) x) +
           ((2 * (j₁ : ℝ) + 2) * (2 * (j₂ : ℝ) + 2) * meanCoeff p.train j₁ * meanCoeff p.train j₂) *
            (lhP p.ν (2 * j₁) x * lhP p.ν (2 * j₂ + 1) x))) • Axi.e3 := by
      intro j₁ _ j₂ _
      rw [← heatPairTermE1_eq_age_smul_Nv p.ν hR0 _ j₂ j₁ τ hz,
        ← heatPairTermE1_eq_age_smul_Nv p.ν hR0 _ j₁ j₂ τ hz,
        UnforcedLeray.Short.IIb.ChartJetsAux.Nv_eq_fun,
        UnforcedLeray.Short.IIb.ChartJetsAux.Nv_eq_fun]
      dsimp only
      rw [map_smul, map_smul, frameL_meridE1, smul_smul, smul_smul, smul_smul, smul_smul,
        ← add_smul]
      congr 1
      dsimp [x]
      ring
    have hsum1 :
        (∑ j₁ ∈ Finset.range (N + 1), ∑ j₂ ∈ Finset.range (N + 1),
          (heatPairTermE1 p.ν p.R
            (ringEps p.R ^ 2 * (-(2 * (j₂ : ℝ)) * (2 * (j₂ : ℝ) + 2) *
              meanCoeff p.train j₁ * meanCoeff p.train j₂)) j₂ j₁ z +
           heatPairTermE1 p.ν p.R
            (ringEps p.R ^ 2 * ((2 * (j₁ : ℝ) + 2) * (2 * (j₂ : ℝ) + 2) *
              meanCoeff p.train j₁ * meanCoeff p.train j₂)) j₁ j₂ z)) =
        (Axi.age p.R z * Real.sqrt (Axi.age p.R z) *
          (ringEps p.R ^ 2 * b2Form (S_heat N) (S_heat N) p.ν p.c p.train x)) • Axi.e3 := by
      rw [hheat, Finset.mul_sum, Finset.mul_sum, Finset.sum_smul]
      refine Finset.sum_congr rfl fun j₁ hj₁ => ?_
      rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_smul]
      refine Finset.sum_congr rfl fun j₂ hj₂ => ?_
      rw [hterms j₁ hj₁ j₂ hj₂]
      congr 1
      ring
    rw [hsum1, frameL_meridE1, smul_smul, smul_smul]
  rw [UnforcedLeray.Short.IIb.ChartJetsAux.Nv_eq_fun,
    UnforcedLeray.Short.IIb.ChartJetsAux.Nv_eq_fun]
  dsimp only
  rw [map_smul, map_smul, hF_eq]
  change Axi.age p.R z • (Real.sqrt (Axi.age p.R z) •
      ((ringEps p.R ^ 2 * Jet.B2.meanB2 p.ν p.c p.train x) •
        Axi.frameL z LateHeatDecomp2Sub.meridE1)) = _
  rw [hsplit, left_distrib, add_smul, smul_add]
  dsimp [x]
  exact smul_add _ _ _

/-! ### 7. Iterated `K^k ∂_η^j` bounds from `Jet.JQ` and assembly of `BlockB2` -/

theorem jq_famEta_iter : ∀ (j n : ℕ) (a : ℝ) (F : Jet.Fam),
    Jet.JQ (n + j) a F →
    Jet.JQ n a (fun ν c tr => partialEta^[j] (F ν c tr))
  | 0, n, a, F, h => by simpa using h
  | j + 1, n, a, F, h => by
    have h' : Jet.JQ ((n + 1) + j) a F := by rw [Nat.add_right_comm]; exact h
    have ih :=
      Jet.jetToolkit.jc.qmono (a' := a) (by linarith) (jq_famEta_iter j (n + 1) a F h').eta
    have heq : Jet.famEta (fun ν c tr => partialEta^[j] (F ν c tr)) =
        fun ν c tr => partialEta^[j + 1] (F ν c tr) := by
      funext ν c tr
      exact (Function.iterate_succ_apply' partialEta j (F ν c tr)).symm
    rwa [heq] at ih

theorem jq_famK_iter : ∀ (k n : ℕ) (a : ℝ) (F : Jet.Fam),
    Jet.JQ (n + k) a F →
    Jet.JQ n a (fun ν c tr => ageOperator^[k] (F ν c tr))
  | 0, n, a, F, h => by simpa using h
  | k + 1, n, a, F, h => by
    have h' : Jet.JQ ((n + 1) + k) a F := by rw [Nat.add_right_comm]; exact h
    have ih := (jq_famK_iter k (n + 1) a F h').k
    have heq : Jet.famK (fun ν c tr => ageOperator^[k] (F ν c tr)) =
        fun ν c tr => ageOperator^[k + 1] (F ν c tr) := by
      funext ν c tr
      exact (Function.iterate_succ_apply' ageOperator k (F ν c tr)).symm
    rwa [heq] at ih

theorem remB2_word_WW (N k j : ℕ) :
    Jet.WW (N : ℝ) (fun ν c tr => ageOperator^[k] (partialEta^[j] (remB2 N ν c tr))) :=
  (jq_famK_iter k 0 (N : ℝ) _
    (jq_famEta_iter j (0 + k) (N : ℝ) (remB2 N) (remB2_JQ N (0 + k + j)))).ww

/-- Core assembly of the Block `B₂` late heat split at order `N` from a viscosity threshold
`ν₀ > 0` for the `(m ≤ 4, k ≤ 2, j ≤ 4)` words of `remB2 N`. -/
theorem meanBlockB2_split_of_words_at (N : ℕ) {ν₀ : ℝ} (hν₀ : 0 < ν₀)
    (hWords : ∀ q : Fin 5 × Fin 3 × Fin 5, ∃ (C : ℝ) (d : ℕ),
      ∀ ν : ℝ, 0 < ν → ν ≤ ν₀ →
        ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-(2 : ℝ))), IsBUCTrain tr →
          WtdBound q.1.val
            (ageOperator^[q.2.1.val] (partialEta^[q.2.2.val] (remB2 N ν (ν ^ (-(2 : ℝ))) tr)))
            (N : ℝ) (polyConst C d ν (ν ^ (-(2 : ℝ)))))
    (p : Params) (htr : IsBUCTrain p.train) (hν : p.ν < ν₀)
    (hc : p.c = (p.ν ^ 2)⁻¹) (hR : 2 ≤ p.R) :
    ∃ (F_heat : UnforcedLeray.Space → UnforcedLeray.Space)
      (f_rem : ProfilePoint → ℝ) (C_heat B : ℝ),
      0 ≤ B ∧
      ContDiff ℝ ∞ F_heat ∧
      ContDiffOn ℝ ∞ f_rem ageDomain ∧
      (∀ (τ : ℝ) (z : UnforcedLeray.Space), z ∉ Axi.axis →
        Axi.age p.R z • Axi.Nv p.R
          (fun m => (ringEps p.R ^ 2 * Jet.B2.meanB2 p.ν p.c p.train (chartSwap m)) •
            LateHeatDecomp2Sub.meridE1) τ z =
          F_heat z + Axi.age p.R z • Axi.Nv p.R
            (fun m => f_rem (chartSwap m) • LateHeatDecomp2Sub.meridE1) τ z) ∧
      (∀ y : UnforcedLeray.Space, Axi.ϱ y ≤ p.R →
        (1 + y 2 ^ 2) * ‖iteratedFDeriv ℝ 2 F_heat y‖ ≤ C_heat) ∧
      (∀ x : ProfilePoint, 1 ≤ x.2.2 → ∀ ℓ ≤ 2, ∀ a ≤ 2, ∀ b ≤ 2,
        (1 + x.2.1 ^ 2 / x.2.2) ^ 2 *
          |(partialAge^[ℓ] (partialEta^[a] (partialQ^[b] f_rem))) x| ≤ B * x.2.2 ^ (-(N : ℝ))) := by
  let _ := hν₀
  obtain ⟨hF_sm, C_heat, _, hF_bd⟩ := F_heat_B2_smooth_and_jet2 p N
  let g_rem : ProfilePoint → ℝ := remB2 N p.ν p.c p.train
  let f_rem : ProfilePoint → ℝ := fun x => ringEps p.R ^ 2 * g_rem x
  have hg_sm : ContDiffOn ℝ ∞ g_rem ageDomain :=
    (remB2_JQ N 0).smooth p.ν p.c p.ν_pos p.c_pos p.train htr
  have hf_sm : ContDiffOn ℝ ∞ f_rem ageDomain := contDiffOn_const.mul hg_sm
  have hf_q : ∀ y ∈ ageDomain, partialQ f_rem y = 0 :=
    fun y hy => ((qInv_remB2 N p.ν p.c p.train).const_mul (ringEps p.R ^ 2)).partialQ_eq_zero hf_sm hy
  choose C_q d_q H_q using hWords
  have hc_rpow : p.c = p.ν ^ (-(2 : ℝ)) := by
    rw [hc, show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg p.ν_pos.le, Real.rpow_natCast]
  have hWtd_q : ∀ q : Fin 5 × Fin 3 × Fin 5,
      WtdBound q.1.val (ageOperator^[q.2.1.val] (partialEta^[q.2.2.val] g_rem))
        (N : ℝ) (polyConst (C_q q) (d_q q) p.ν p.c) := by
    intro q
    have hgen : ∀ (c : ℝ) (tr : UnforcedLeray.B0140.TrainSol p.ν c),
        c = p.ν ^ (-(2 : ℝ)) → IsBUCTrain tr →
        WtdBound q.1.val (ageOperator^[q.2.1.val] (partialEta^[q.2.2.val] (remB2 N p.ν c tr)))
          (N : ℝ) (polyConst (C_q q) (d_q q) p.ν c) := by
      rintro _ tr rfl htr'
      exact H_q q p.ν p.ν_pos hν.le tr htr'
    exact hgen p.c p.train hc_rpow htr
  set B₀ : ℝ := ∑ q : Fin 5 × Fin 3 × Fin 5, max (polyConst (C_q q) (d_q q) p.ν p.c) 0
  have hB₀ : 0 ≤ B₀ := Finset.sum_nonneg fun q _ => le_max_right _ _
  refine ⟨F_heat_B2 p N, f_rem, C_heat, 9 * B₀, mul_nonneg (by norm_num) hB₀,
    hF_sm, hf_sm, fun τ z hz => meanB2_lift_decomp p htr hR N τ hz, hF_bd, ?_⟩
  intro x hx1
  have hx0 : x ∈ ageDomain := lt_of_lt_of_le one_pos hx1
  obtain ⟨hε0, hε1⟩ := ringEps_nonneg_and_le_one hR
  have hε20 : 0 ≤ ringEps p.R ^ 2 := sq_nonneg _
  have hε21 : ringEps p.R ^ 2 ≤ 1 := by nlinarith
  have hBN0 : 0 ≤ B₀ * x.2.2 ^ (-(N : ℝ)) :=
    mul_nonneg hB₀ (Real.rpow_nonneg hx0.le _)
  have hK_jets : ∀ m ≤ 4, ∀ k ≤ 2, ∀ j ≤ 4,
      (1 + x.2.1 ^ 2 / x.2.2) ^ m * |(ageOperator^[k] (partialEta^[j] f_rem)) x| ≤
        B₀ * x.2.2 ^ (-(N : ℝ)) := by
    intro m hm k hk j hj
    let q : Fin 5 × Fin 3 × Fin 5 := (⟨m, by omega⟩, ⟨k, by omega⟩, ⟨j, by omega⟩)
    have hlin := Jet.jetToolkit.iterLin.2.2 g_rem hg_sm (ringEps p.R ^ 2) k j 0 hx0
    simp only [Function.iterate_zero, id_eq] at hlin
    change (ageOperator^[k] (partialEta^[j] f_rem)) x =
      ringEps p.R ^ 2 * (ageOperator^[k] (partialEta^[j] g_rem)) x at hlin
    have habs_le : |(ageOperator^[k] (partialEta^[j] f_rem)) x| ≤
        |(ageOperator^[k] (partialEta^[j] g_rem)) x| := by
      rw [hlin, abs_mul, abs_of_nonneg hε20]
      exact mul_le_of_le_one_left (abs_nonneg _) hε21
    have hq_le : max (polyConst (C_q q) (d_q q) p.ν p.c) 0 ≤ B₀ :=
      Finset.single_le_sum (fun i _ => le_max_right (polyConst (C_q i) (d_q i) p.ν p.c) 0)
        (Finset.mem_univ q)
    have hbd_q : (1 + x.2.1 ^ 2 / x.2.2) ^ m * |(ageOperator^[k] (partialEta^[j] g_rem)) x| ≤
        B₀ * x.2.2 ^ (-(N : ℝ)) :=
      ((hWtd_q q x hx1).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hx0.le _))).trans
        (mul_le_mul_of_nonneg_right hq_le (Real.rpow_nonneg hx0.le _))
    exact (mul_le_mul_of_nonneg_left habs_le (by positivity)).trans hbd_q
  intro ℓ hℓ a ha b hb
  have hpart := wtd_partials_of_K_eta_jets hf_sm hf_q hx1 hBN0 hK_jets ℓ hℓ a ha b hb
  linarith

end BlockB2Sub

/-- **Unconditional fixed-order `N` late heat decomposition for Block `B₂`**. -/
theorem meanBlockB2LateHeatSplit2_at (N : ℕ) :
    ScalarMeridLateHeatSplit2At
      (fun p x => ringEps p.R ^ 2 * Jet.B2.meanB2 p.ν p.c p.train x)
      LateHeatDecomp2Sub.meridE1 N := by
  choose C_q d_q ν_q hν_q H_q using fun q : Fin 5 × Fin 3 × Fin 5 =>
    BlockB2Sub.remB2_word_WW N q.2.1.val q.2.2.val 2 q.1.val (by norm_num)
  obtain ⟨ν₀, hν₀, hle⟩ : ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ q : Fin 5 × Fin 3 × Fin 5, ν₀ ≤ ν_q q := by
    refine ⟨Finset.univ.inf' Finset.univ_nonempty ν_q, ?_, fun q =>
      Finset.inf'_le ν_q (Finset.mem_univ q)⟩
    rw [Finset.lt_inf'_iff]
    intro q _
    exact hν_q q
  refine ⟨ν₀, hν₀, fun p htr hν hc hR _ => ?_⟩
  exact BlockB2Sub.meanBlockB2_split_of_words_at N hν₀
    (fun q => ⟨C_q q, d_q q, fun ν hν0 hνle tr htr' =>
      H_q q ν hν0 (hνle.trans (hle q)) tr htr'⟩)
    p htr hν hc hR

/-- **Target `MeanBlockB2LateHeatSplit2` (`PartIII-b:C/ward/12/3/2/2/1/2/1/2/4`).** -/
theorem meanBlockB2LateHeatSplit2 : MeanBlockB2LateHeatSplit2 :=
  meanBlockB2LateHeatSplit2_at

end UnforcedLeray.Short.PartIIIb.Concrete
