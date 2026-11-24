import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Sub.ConvEnvSub

/-!
# `CKCongr`: `𝒦` at `s > 0` depends only on the profile on `s' > 0`
(source 5034-5044; `Kop` uses `deriv` in `s`, which is local).
-/

set_option autoImplicit false

noncomputable section

open Filter Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- One scalar component: `Kop` at `s > 0` is unchanged when the profile is changed off `s' > 0`. -/
private theorem kop_congr_aux (f g : ℝ → ℝ × ℝ → ℝ)
    (h : ∀ s' : ℝ, 0 < s' → ∀ y : ℝ × ℝ, f s' y = g s' y)
    (s : ℝ) (hs : 0 < s) (x : ℝ × ℝ) : Kop f s x = Kop g s x := by
  have hfun : f s = g s := funext (h s hs)
  have hder : deriv (fun s' => f s' x) s = deriv (fun s' => g s' x) s := by
    apply Filter.EventuallyEq.deriv_eq
    exact Filter.eventually_of_mem (Ioi_mem_nhds hs) (fun s' hs' => h s' hs' x)
  unfold Kop
  rw [hfun, hder]

theorem ckCongr : CKCongr := by
  intro F G h s hs x
  unfold cK
  exact Prod.ext
    (kop_congr_aux (fun s' y => (F s' y).1) (fun s' y => (G s' y).1)
      (fun s' hs' y => congrArg Prod.fst (h s' hs' y)) s hs x)
    (kop_congr_aux (fun s' y => (F s' y).2) (fun s' y => (G s' y).2)
      (fun s' hs' y => congrArg Prod.snd (h s' hs' y)) s hs x)

end UnforcedLeray.Short.PartIIIb.Concrete
