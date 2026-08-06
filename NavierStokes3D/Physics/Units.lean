set_option autoImplicit false

namespace NavierStokes3D.Physics

structure Length where
  val : ℝ

structure Time where
  val : ℝ

structure Mass where
  val : ℝ

structure Velocity where
  val : ℝ

structure Acceleration where
  val : ℝ

structure Force where
  val : ℝ

structure Pressure where
  val : ℝ

structure Density where
  val : ℝ

structure DynamicViscosity where
  val : ℝ

structure KinematicViscosity where
  val : ℝ

def mToCm (m : Length) : Length := ⟨m.val * 100⟩

def cmToM (cm : Length) : Length := ⟨cm.val / 100⟩

end NavierStokes3D.Physics
