(module
  (type (;0;) (func (param i32)))
  (type (;1;) (func (param i32) (result i32 i32)))
  (type (;2;) (func (result i32)))
  (type (;3;) (func (param i32 i32) (result i32)))
  (type (;4;) (func (param i32 i32 i32) (result i32)))
  (type (;5;) (func (param i64) (result i32)))

  ;; (export "multiple-return" (func 0))
  (func (;0;) (type 1) (param i32) (result i32 i32)
    i32.const 0
    i32.const 1)

  ;; (export "block" (func 1))
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

  (table (;0;) 1 1 funcref)
  (memory (;0;) 2)
  (global (;0;) (mut i32) (i32.const 66560))
  (export "memory" (memory 0)))
