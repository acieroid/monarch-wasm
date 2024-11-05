(module
  (type (;0;) (func (param i32)))
  (type (;1;) (func (param i32) (result i32 i32)))
  (type (;2;) (func (result i32)))
  (type (;3;) (func (param i32 i32) (result i32)))
  (type (;4;) (func (param i32 i32 i32) (result i32)))
  (type (;5;) (func (param i64) (result i32)))

  (export "multiple-return" (func 0))
  (func (;0;) (type 1) (param i32) (result i32 i32)
    i32.const 0
    i32.const 1)

  (export "block" (func 1))
  (func (;1;) (type 2) (param) (result i32)
    block (result i32)
      i32.const 1
    end)

  (export "br" (func 2))
  (func (;2;) (type 2) (param) (result i32)
    block
      br 0
    end
    i32.const 0)

  (export "br-with-stack" (func 3))
  (func (;3;) (type 2) (param) (result i32)
    block (result i32)
      i32.const 0
      br 0
    end)

  (export "br-with-stack-two-values" (func 4))
  (func (;4;) (type 2) (param) (result i32)
    block (result i32 i32)
      i32.const 1
      i32.const 2
      br 0
    end
    drop)

  (export "globals" (func 5))
  (func (;5;) (type 2) (param) (result i32)
    i32.const 42
    global.set 0
    global.get 0)

  (export "memory" (func 6))
  (func (;6;) (type 2) (param) (result i32)
    i32.const 42
    f64.load
    f64.const 0
    f64.mul
    drop
    i32.const 0)

  (table (;0;) 1 1 funcref)
  (memory (;0;) 2)
  (global (;0;) (mut i32) (i32.const 66560))
  (export "memory" (memory 0)))
