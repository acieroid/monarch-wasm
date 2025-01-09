(module
  (type (;0;) (func (param i32) (result i32)))

  (export "br-with-stack-two-values" (func 0))
  (func (;0;) (type 0) (param i32) (result i32)
    block (result i32 i32)
      i32.const 1
      i32.const 2
      br 0
    end
    drop)

  (table (;0;) 1 1 funcref)
  (memory (;0;) 2)
  (global (;0;) (mut i32) (i32.const 66560))
  (export "memory" (memory 0)))
