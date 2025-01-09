(module
  (type (;0;) (func (param i32) (result i32)))

  (export "return-from-block" (func 0))
  (func (;0;) (type 0) (param i32) (result i32)
    i32.const 0
    block
      i32.const 20
      return
    end) ;; should result in 20

  (table (;0;) 1 1 funcref)
  (memory (;0;) 2)
  (global (;0;) (mut i32) (i32.const 66560))
  (export "memory" (memory 0)))
