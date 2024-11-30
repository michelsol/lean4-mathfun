import Lake
open Lake DSL

package mathfun where
  packagesDir := "/tmp/lean4-mathfun/packages"
  buildDir := "/tmp/lean4-mathfun/build"
  -- add package configuration options here

@[default_target]
lean_lib MathFun where
  srcDir := "src"

-- @[default_target]
lean_exe Main where
  srcDir := "tests"

require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "746714471ae87031bebd4bcdbc49f2aae01cae8f"

