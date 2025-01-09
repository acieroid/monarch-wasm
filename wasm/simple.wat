(module
  (type (;0;) (func (param i32)))
  (type (;1;) (func (param i32) (result i32 i32)))
  (type (;2;) (func (result i32)))
  (type (;3;) (func (param i32 i32) (result i32)))
  (type (;4;) (func (param i32 i32 i32) (result i32)))
  (type (;5;) (func (param i64) (result i32)))
  (type (;6;) (func (param i32) (result i32)))

  (export "multiple-return" (func 0))
  (func (;0;) (type 1) (param i32) (result i32 i32)
    i32.const 0
    i32.const 1) ;; should return [1, 0]

  (export "block" (func 1))
  (func (;1;) (type 2) (param) (result i32)
    block (result i32)
      i32.const 1
    end) ;; should return 1

  (export "br" (func 2))
  (func (;2;) (type 2) (param) (result i32)
    block
      br 0
    end
    i32.const 0) ;; should return 0

  (export "br-with-stack" (func 3))
  (func (;3;) (type 2) (param) (result i32)
    block (result i32)
      i32.const 0
      br 0
    end) ;; should return 0

  (export "br-with-stack-two-values" (func 4))
  (func (;4;) (type 2) (param) (result i32)
    block (result i32 i32)
      i32.const 1
      i32.const 2
      br 0
    end
    drop) ;; should return 1

  (export "globals" (func 5))
  (func (;5;) (type 2) (param) (result i32)
    i32.const 42
    global.set 0
    global.get 0) ;; should return 42

  (export "mem" (func 6))
  (func (;6;) (type 2) (param) (result i32)
    i32.const 42
    f64.load
    f64.const 0
    f64.mul
    drop
    i32.const 0) ;; should return 0

  (export "select" (func 7))
  (func (;7;) (type 2) (param) (result i32)
    i32.const 10
    i32.const 20
    i32.const 0
    select) ;; should result in 20

  (export "return" (func 8))
  (func (;8;) (type 2) (param) (result i32)
    i32.const 20
    return) ;; should result in 20

  (export "return-from-block" (func 9))
  (func (;9;) (type 2) (param) (result i32)
    i32.const 0
    block
      i32.const 20
      return
    end) ;; should result in 20

  (export "id" (func 10))
  (func (;10;) (type 6) (param i32) (result i32)
    local.get 0
    return) ;; returns its argument

  (export "call" (func 11))
  (func (;11;) (type 2) (param) (result i32)
    i32.const 4242
    call 10) ;; calling identity function, should result in 42

  (export "single-return" (func 12))
  (func (;0;) (type 6) (param i32) (result i32)
    i32.const 0
    i32.const 1
    drop) ;; should return [0]

  (table (;0;) 1 1 funcref)
  (memory (;0;) 2)
  (global (;0;) (mut i32) (i32.const 66560))
  (export "memory" (memory 0)))
