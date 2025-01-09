(module
  (type (;0;) (func (param i32) (result i32)))

  (export "fun0" (func 0))
  (func (;0;) (type 0) (param i32) (result i32)
    i32.const 0
    call 1) ;; should return [1]

  (export "fun1" (func 1))
  (func (;1;) (type 0) (param i32) (result i32)
    i32.const 1
    return) ;; should return [1]

  (table (;0;) 1 1 funcref)
  (memory (;0;) 2)
  (global (;0;) (mut i32) (i32.const 66560))
  (export "memory" (memory 0)))
