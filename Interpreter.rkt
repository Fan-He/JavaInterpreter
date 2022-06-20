#lang racket

;Author: Xiaofan He, Joey Li, Miracle Hunt


(require "classParser.rkt")

;The overall method
;takes a list and a table as input
;Recursivly call on the input commands until return
(define M_overall_cc
  (lambda (lis table break next jump parentjump exit parent return)
    (cond
      [(null? lis) null]
      [(not (list? table)) table]
      [(null? (cdr lis)) (M_state (get_oa lis) table break next jump parentjump exit parent return)]
      [else (M_overall_cc (cdr lis) (M_state (get_oa lis) table break next jump parentjump exit parent return) break next jump parentjump exit parent return)])))

(define M_overall
 (lambda (lis table break next jump parentjump exit parent)
   (call/cc (lambda (return) (M_overall_cc lis table break next jump parentjump exit parent return)))))

;takes a list as input
;return whether the return type of the list is boolean
(define isBoolean
  (lambda (lis)
    (cond
      [(and (not (list? lis)) (or (eq? lis 'false) (eq? lis 'true))) #t]
      [(not (list? lis)) #f]
      [(or (or (or (or (or (or (or (or (eq? (get_oa lis) '<) (eq? (get_oa lis) '>)) (eq? (get_oa lis) '<=)) (eq? (get_oa lis) '>=)) (eq? (get_oa lis) '==)) (eq? (get_oa lis) '&&))(eq? (get_oa lis) '||))(eq? (get_oa lis) '!))(eq? (get_oa lis) '!=))
       #t]
      [else #f])))


;generate a new binding table
(define newTable
  (lambda ()
    '(((() ())))))

;return state
(define M_return
  (lambda (lis globalTable table table2 break next jump parentjump exit parent return)
    (cond
      ;if the return is a var, return its value
      [(eq? 'true (oad lis)) (return (list #t (list globalTable (list table table2))))]
      [(eq? 'false (oad lis)) (return (list #f (list globalTable (list table table2))))]
      [(and (not (list? (expression1 lis))) (not (number? (expression1 lis))))
       (cond
        [(contains table (expression1 lis)) (if (number? (getBinding table (expression1 lis))) (return (list (getBinding table (expression1 lis)) (list globalTable (list table table2))))
                                                ;convert #t and # f to true and false
                                                (if (eq? #t (getBinding table (expression1 lis))) (return (list #t (list globalTable (list table table2))))
                                                    (return (list #f (list globalTable (list table table2))))))]
        [else (error "using before declaring")])]
      ;convert #t and # f to true and false
      [(isBoolean (expression1 lis))
       (if (get_oa (M_boolean (expression1 lis) globalTable table table2 break next jump parentjump exit parent return)) (return (list #t (cadr (M_boolean (expression1 lis) globalTable table table2 break next jump parentjump exit parent return))))
       (return (list #f (oad (M_boolean (expression1 lis) globalTable table table2 break next jump parentjump exit parent return)))))]
      ;return math expression value
      [else (return (M_value (expression1 lis) globalTable table table2 break next jump parentjump exit parent return))])))


;modify binding in the input third layer table
(define modify_binding_inner
  (lambda (table var value)
    (cond
      ;null check
      [(null? (get_oa table)) '(() ())]
      ;if the first var in the table is the input var, modify the corresponding value
      [(eq? (get_oa (get_oa table)) var) (cons (get_oa table) (cons (cons value (get_od (get_oa (get_od table)))) '()))]
      ;if the first var of the table is not the input var, continue checking and cons the current var and value to the list
      [else (cons (cons (get_oa (get_oa table)) (get_oa (modify_binding_inner (cons (get_od (get_oa table)) (cons (get_od (get_oa (get_od table))) '())) var value))) (cons (cons (get_oa (get_oa (get_od table))) (get_oa (get_od (modify_binding_inner (cons (get_od (get_oa table)) (cons (get_od (get_oa (get_od table))) '())) var value)))) '()))])))

;modify the binding in the input second layer table
(define modify_binding_helper
  (lambda (table var value)
    (cond
      [(null? table) (error "modifing before declaring")]
      [(eq? #f (contains_inner (get_oa table) var)) (cons (get_oa table) (modify_binding_helper (get_od table) var value))]
      [else (cons (modify_binding_inner (get_oa table) var value) (get_od table))])))

;Modify binding table and return the modified table
;takes a table, a variable name, and a value as input
;put the value to the place corresponding to the position of the var in the table
(define modify_binding
  (lambda (table var value)
    (cond
      [(null? table) (error "modifying before declaring")]
      [(eq? #t (contains_helper (get_oa table) var))
       (if (contains (get_od table) var)
           (cons (get_oa table)(modify_binding (get_od table) var value))
           (cons (modify_binding_helper (get_oa table) var value) (get_od table)))]
      [(eq? #f (contains_helper (get_oa table) var)) (cons (get_oa table) (modify_binding (get_od table) var value))]
      ;[else (cons (modify_binding_helper (get_oa table) var value) (get_od table))]
      )))

(define changeFieldValue
  (lambda (valuelist index newValue)
    (cond
      [(eq? 0 index) (cons newValue (get_od valuelist))]
      [else (cons (get_oa valuelist) (changeFieldValue (get_od valuelist) (- index 1) newValue))])))

;input (= (dot this x) 2)
(define modifyBinding_globalandlocal
  (lambda (lis globalTable table table2)
    (cond
      [(eq? 'this (oad (oad lis))) (modify_binding table 'this (cons (get_oa (getBinding table 'this)) (cons (oad (getBinding table 'this)) (list (changeFieldValue (oadd (getBinding table 'this)) (getFirstBindingVar_3 (oadd (oad lis)) (caadr (oad (getBinding table 'this)))) (get_oa (M_value (oadd lis) globalTable table table2 'break 'next 'jump 'parentjump 'exit 'parent 'return)))))))]
      [else (modify_binding table (cadadr lis) (cons (get_oa (getBinding table (cadadr lis))) (cons (oad (getBinding table (cadadr lis))) (list (changeFieldValue (oadd (getBinding table (cadadr lis))) (getFirstBindingVar_3 (oadd (oad lis)) (caadr (oad (getBinding table (cadadr lis))))) (get_oa (M_value (oadd lis) globalTable table table2 'break 'next 'jump 'parentjump 'exit 'parent 'return)))))))])))
      

;Initialize state
;Assign a value to a declared variable
(define M_init
  (lambda (lis globalTable table table2 break next jump parentjump exit parent return)
    (cond
      [(list? (oad lis)) (list globalTable (list (modifyBinding_globalandlocal lis globalTable table table2) table2))]
      [else
       ;if the variable has been declared, assign a value to it
       (if (contains table (get_oa (get_od lis)))
        (if (isBoolean (get_oa (get_od (get_od lis))))
            ;check the return type of the value to be assigned and send them to corresponding states
            (list globalTable (list (modify_binding (varTable (oad (M_boolean (get_oa (get_od (get_od lis))) globalTable table table2 break next jump parentjump exit parent return))) (var_name lis) (get_oa (M_boolean (get_oa (get_od (get_od lis))) globalTable table table2 break next jump parentjump exit parent return)))
                  (funcTable (oad (M_boolean (get_oa (get_od (get_od lis))) globalTable table table2 break next jump parentjump exit parent return)))))
            (list globalTable (list (modify_binding (varTable (oad (M_value (get_oa (get_od (get_od lis))) globalTable table table2 break next jump parentjump exit parent return))) (var_name lis) (get_oa (M_value (get_oa (get_od (get_od lis))) globalTable table table2 break next jump parentjump exit parent return))) (funcTable (cadr (M_value (get_oa (get_od (get_od lis))) globalTable table table2 break next jump parentjump exit parent return))))))
        ;if the variable has not been declared, raise an error
        (M_init (cons (get_oa lis) (list (cons 'dot (list 'this (oad lis))) (caddr lis))) globalTable table table2 break next jump parentjump exit parent return))])))
        

       
    
(define var_name
  (lambda (lis)
    (get_oa (get_od lis))))

;get the value of a variable from the binding table
(define getBinding_inner
  (lambda (table var)
    (cond
      ;if the var is not in the table, raise an error
      [(null? (get_oa table)) (error "using before declaring")]
      [(null? (get_oa (get_od table))) null]
      [(eq? var (get_oa (get_oa table))) (if (eq? (get_oa (get_oa (get_od table))) 'null)
                                       ;if the value is null, raise an error
                                       (error "using before assigning")
                                       (get_oa (get_oa (get_od table))))]
      [else (getBinding_inner (cons (get_od (get_oa table)) (cons (get_od (get_oa (get_od table))) '())) var)])))

;check if the input first layer table contains the input var
(define contains
  (lambda (table var)
    (cond
      [(null? table) #f]
      [(contains_helper (get_oa table) var) #t]
      [else (contains (get_od table) var)])))

(define contains_second
  (lambda (table var)
    (cond
      [(null? table) #f]
      [(null? (get_od table)) (contains_helper (get_oa table) var)]
      [else (contains_second (get_od table) var)])))

;check if the input second layer table contains the input var
(define contains_helper
  (lambda (table var)
    (cond
      [(null? table) #f]
      [(contains_inner (get_oa table) var) #t]
      [else (contains_helper (get_od table) var)])))

;check if the input table contains the input var
(define contains_inner
  (lambda (table var)
    (cond
      [(null? (get_oa table)) #f]
      [(eq? var (get_oa (get_oa table))) #t]
      [else (contains_inner (cons (get_od (get_oa table)) (get_od table)) var)])))

;get binding helper method
;get the binding in the second layer table
(define getBinding_helper
  (lambda (table var)
    (cond
      [(null? table) (error "using before declaring")]
      [(eq? #f (contains_inner (get_oa table) var)) (getBinding_helper (get_od table) var)]
      [else (getBinding_inner (get_oa table) var)])))

;get binding in the first layer table, which is the main table
(define getBinding
  (lambda (table var)
    (cond
      [(null? table) 'no]
      [(eq? #t (contains_helper (get_oa table) var))
       (if (contains (get_od table) var)
           (getBinding (get_od table) var)
           (getBinding_helper (get_oa table) var))]
      [(eq? #f (contains_helper (get_oa table) var)) (getBinding (get_od table) var)]
      ;[else (getBinding_helper (get_oa table) var)]
      )))

;interpret method, takes a file name as input
(define interpret
  (lambda (name)
    (cond
      [(null? name) 0]
      [else (get_oa (M_main (M_overall (parser name) (list '(() ()) (list (newTable) '((() ())))) 'nobreak '() 'nojump 'noparentjump 'noexit 'invalid)))])))

; return class closure
(define getLastClass
  (lambda (className classClosure)
    (cond
     [(null? (get_od className)) (get_oa classClosure)]
     [else (getLastClass (get_od className) (get_od classClosure))])))

; return func body
(define findMainBody
  (lambda (globalTable)
    (oad (getFirstBindingFunc_3 'main
                           (getMethod_Name_ListFromClassClosure (getLastClass (get_oa globalTable) (oad globalTable)))
                           (getMethod_Closure_ListFromClassClosure (getLastClass (get_oa globalTable) (oad globalTable)))))))

(define M_main
  (lambda (table) ;(global (table table2))
    (M_overall (findMainBody (get_oa table)) table 'nobreak '() 'nojump 'noparentjump 'noexit 'invalid)))
               
;delete binding
(define delete_binding_one
  (lambda (table)
    (cond
      [(null? table) '()]
      [(null? (get_od table)) '()]
      [else (cons (get_oa table) (delete_binding_one (get_od table)))])))

(define delete_binding
  (lambda (table)
    (if (null? table)
        table
        (list (delete_binding_one (get_oa table)) (oad table)))))


;State layer: the main program is initialized with a first layer table
;each time a while is called, a new second layer table is added
;when each while ends, delete the last second layer table, which is created for this while loop
;for if/try/catch/finally, a new third layer table is added
;after each ends, delete the last third layer table which is created for it




;declare state
;declares a variable by putting it in the binding table
;if no value assigned, set the value to null
;return the binding table after declaring
(define M_declare
  (lambda (lis globalTable table table2 break next jump parentjump exit parent return)
    (cond
      [(null? lis) (list table table2)]
      [(contains_second table (expression1 lis)) (error "Already declared")]
      ;if only declare
      [(null? (get_od (get_od lis))) (list (addBinding table (expression1 lis) 'null) table2)]
      ;bind the value to the var name
      [else (if (isBoolean (get_oa (get_od (get_od lis))))
                (list globalTable (list (addBinding (getInnerVarTable (M_boolean (expression2 lis) globalTable table table2 break next jump parentjump exit parent return)) (expression1 lis) (get_oa (M_boolean (expression2 lis) globalTable table table2 break next jump parentjump exit parent return))) (getInnerVarTable2 (M_boolean (expression2 lis) globalTable table table2 break next jump parentjump exit parent return))))
                (list globalTable (list (addBinding (getInnerVarTable (M_value (expression2 lis) globalTable table table2 break next jump parentjump exit parent return)) (expression1 lis) (get_oa (M_value (expression2 lis) globalTable table table2 break next jump parentjump exit parent return))) (getInnerVarTable2 (M_value (expression2 lis) globalTable table table2 break next jump parentjump exit parent return)))))]
      )))

;the input list has patter: (operator <exp1> <exp2>)
;return the operator of the input list
(define operator
  (lambda (lis)
    (get_oa lis)))

;the input list has patter: (operator <exp1> <exp2>)
;return the exp1 of the input list
(define expression1
  (lambda (lis)
    (get_oa (get_od lis))))

;the input list has patter: (operator <exp1> <exp2>)
;return the exp2 of the input list
(define expression2
  (lambda (lis)
    (get_oa (cddr lis))))

;add a new binding
(define addBinding_inner
  (lambda (table var value)
    (cons (append (get_oa table) (list var)) (cons (append (get_oa (get_od table)) (list value) ) '()))))

;add a new binding to the last third layer table
(define addBinding
  (lambda (table var value)
    (cond
      ;[(null? (get_od table)) (cons (addBinding_inner (get_oa table) var value) '())]
      [(null? (get_od table)) (list (addBinding_helper (get_oa table) var value))]
      [else (cons (get_oa table) (addBinding (get_od table) var value))])))

;take a second layer table as input
(define addBinding_helper
  (lambda (table var value)
    (cond
      [(null? table) table]
      [(null? (get_od table)) (list (addBinding_inner (get_oa table) var value))]
      [else (cons (get_oa table) (addBinding_helper (get_od table) var value))])))

;delete the last third layer method
(define deep_deleting_one
  (lambda (table)
    (cond
      [(null? table) '()]
      [(null? (get_od table)) (list (delete_last (get_oa table)))]
      [else (cons (get_oa table) (deep_deleting_one (get_od table)))])))

(define deep_deleting
  (lambda (table)
    (if (null? table)
        table
        (cons (deep_deleting_one (get_oa table)) (get_od table)))))

;helper method
(define delete_last
  (lambda (table_2)
    (cond
      [(null? table_2) '()]
      [(null? (get_od table_2)) '()]
      [else (cons (get_oa table_2) (delete_last (get_od table_2)))])))

;add a new third layer table
(define deep_adding
  (lambda (table)
    (cond
      [(null? table) '()]
      [(null? (get_od table)) (cons (add_last (get_oa table)) '())]
      [else (cons (get_oa table) (deep_adding (get_od table)))])))

;helper method
(define add_last
  (lambda (table_2)
    (cond
      [(null? table_2) '((() ()))]
      [else (cons (get_oa table_2) (add_last (get_od table_2)))])))

;add a new second layer table
(define addNewTable
  (lambda (table)
    (append table '(((()()))))))

;add a new second layer table
(define addNewTable_func
  (lambda (table)
    (append table '((()())))))

;get the last inner table in the input table
(define get_last_table
  (lambda (table)
    (cond
      [(null? table) table]
      [(null? (get_od table)) (get_oa table)]
      [else (get_last_table (get_od table))])))

(define varTable
  (lambda (table)
    (get_oa table)))

(define funcTable
  (lambda (table)
    (oad table)))

(define localTable
  (lambda (table)
    (oad table)))

(define classTable
  (lambda (table)
    (get_oa table)))

;before: (x, (table table2))
;after: (x, (globalTable (table table2)))
(define getInnerValue
  (lambda (table)
    (get_oa table)))

(define getInnerGlobalTable
  (lambda (table)
    (get_oa (oad table))))

(define getInnerVarTable
  (lambda (table)
    (get_oa (oad (oad table)))))

(define getInnerVarTable2
  (lambda (table)
    (oad (oad (oad table)))))

(define getInnerWholeTable
  (lambda (table)
    (oad table)))


;control the state
;takes a list as input and send the lists to different state methods by checking the operators
;lis: command
;table: state table
;break: break command of the break and continue, from while loop's call/cc
;next: the next command that the program should go to after the break
;jump: the next place the program should jump to in the try/catch, it is a catch section that the program should go after throw in try
;parentjump: the next place the program should jump to in the try/catch, it is a catch section that the program should go after throw in catch/finally
;exit: exit the current try section due to break/continue/throw
;parent: parent while loop
;return: return the result, empty all the stack
(define M_state
  (lambda (lis table break next jump parentjump exit parent return)
    (cond
      [(null? lis) table]
      ;declare
      [(eq? 'var (operator lis)) (M_declare lis (classTable table) (varTable (localTable table)) (funcTable (localTable table)) break next jump parentjump exit parent return)]
      [(eq? '= (operator lis)) (M_init lis (classTable table) (varTable (localTable table)) (funcTable (localTable table)) break next jump parentjump exit parent return)]
      [(eq? 'if (operator lis)) (deep_deleting (M_if lis (classTable table) (deep_adding (varTable (localTable table))) (funcTable (localTable table)) break next jump parentjump exit parent return))]
      [(eq? 'while (operator lis)) (delete_binding (M_while lis (classTable table) (addNewTable (varTable (localTable table))) (funcTable (localTable table)) next jump parentjump exit return))]
      [(eq? 'begin (operator lis)) (M_overall_cc (get_od lis) table break next jump parentjump exit parent return)]
      [(eq? 'break (operator lis)) (if (null? next) (break table) (break (M_state next table break '() jump parentjump exit parent return)))]
      [(eq? 'continue (operator lis)) (if (null? next) (break (M_while parent (classTable table) (addNewTable (get_oa (delete_binding_one (varTable (localTable table))))) (get_oa (delete_binding_one (funcTable (localTable table)))) next jump parentjump exit return)) (break (M_state next table break '() jump parentjump exit parent return)))]
      [(eq? 'return (operator lis)) (M_return lis (classTable (M_state next table break '() jump parentjump exit parent return)) (varTable (localTable (M_state next table break '() jump parentjump exit parent return))) (funcTable (localTable (M_state next table break '() jump parentjump exit parent return))) break next jump parentjump exit parent return)]
      [(eq? 'try (operator lis)) (deep_deleting (M_try lis (classTable table) (deep_adding (varTable (localTable table))) (deep_adding (funcTable (localTable table))) break next jump parentjump parent return))]
      [(eq? 'throw (operator lis)) (M_throw lis (classTable table) (varTable (localTable table)) (funcTable (localTable table)) break next jump parentjump exit parent return)]
      [(eq? 'catch (operator lis)) (deep_deleting (M_catch lis (classTable table) (varTable (localTable table)) (funcTable (localTable table)) break next jump parentjump exit parent return))]
      [(eq? 'finally (operator lis)) (deep_deleting (M_finally lis (classTable table) (addNewTable (varTable (localTable table))) (funcTable (localTable table)) break next jump parentjump exit parent return))]
      [(eq? 'funcall (operator lis)) (if (list? (get_oa (M_funcall lis (classTable table) (varTable (localTable table)) (funcTable (localTable table)) break next jump parentjump exit parent return)))
                                                (M_funcall lis (classTable table) (varTable (localTable table)) (funcTable (localTable table)) break next jump parentjump exit parent return)
                                                (oad (M_funcall lis (classTable table) (varTable (localTable table)) (funcTable (localTable table)) break next jump parentjump exit parent return)))]
      [(eq? 'function (operator lis)) (M_function lis (varTable (localTable table)) (funcTable (localTable table)) break next jump parentjump exit parent return)]
      [(eq? 'class (operator lis)) (M_class lis (classTable table) (varTable (localTable table)) (funcTable (localTable table)) break next jump parentjump exit parent return)]
      [(or (or (or (or (or (or (or (or (eq? (operator lis) '<) (eq? (operator lis) '>)) (eq? (operator lis) '<=)) (eq? (operator lis) '>=)) (eq? (operator lis) '==)) (eq? (operator lis) '&&))(eq? (operator lis) '||))(eq? (operator lis) '!))(eq? (operator lis) '!=)) (M_boolean lis (classTable table) (varTable (localTable table)) (funcTable (localTable table)))])))

;input for all M functions are table and table2, splited by M_state
;output table of all functions are the combination of table1 and table2
;add a table when initializing them so that now we are using (get_oa table) for places we used to use table
;should modify deep_deleting and delete_binding so that now it deep_delete for both varTable and funcTable of the table


; local -> global
(define M_findBinding
  (lambda (name globalTable table table2)
    (if (eq? 'no (getBinding table name)) (decideDot_var (list 'dot 'this name) globalTable table table2)
        (getBinding table name))))

;Value state
;takes a list or element and a table as input
;return the integer result after calculations
(define M_value
  (lambda (lis globalTable table table2 break next jump parentjump exit parent return)
    (cond
      ;[(null? lis) (list 0 (list table table2))]
      [(not (list? lis))
       (if (number? lis)
           ;if the input is a number, return it
           (list lis (list globalTable (list table table2)))
           ;if the input is a var name, return its value from the binding table
           (list (M_findBinding lis globalTable table table2) (list globalTable (list table table2))))]
      ;if there is only one element in the list
      [(null? (get_od lis))
       ;if that element is a number, return that number
       (if (number? (get_oa lis))
           (list (get_oa lis) (list globalTable (list table table2)))
           ;if that element is a var, return the binded value of that var (pass to mvalue)
           (list (get_oa (M_value (get_oa lis) globalTable table table2 break next jump parentjump exit parent return)) (list globalTable (list table table2))))]
      [(eq? 'dot (get_oa lis))
       (list (decideDot_var lis globalTable table table2) (list globalTable (list table table2)))]
      [(eq? 'funcall (operator lis))
       (if ( list? ( get_oa (funcall_v lis globalTable table table2 exit jump) ))
           (error "bad operation: no return statement in function call")
           (funcall_v lis globalTable table table2 exit jump))]
      [(eq? '+ (operator lis)) (exec_operator + lis globalTable table table2 break next jump parentjump exit parent return)]
      [(eq? '- (operator lis)) (if (null? (cddr lis))
                               ;if it is only negation
                              (list (get_oa (* -1 (M_value (expression1 lis) globalTable table table2 break next jump parentjump exit parent return))) (oad (M_value (expression1 lis) globalTable table table2 break next jump parentjump exit parent return)))
                              ;if it is minus
                              (exec_operator - lis globalTable globalTable table table2 break next jump parentjump exit parent return))]
      [(eq? '* (operator lis)) (exec_operator * lis globalTable table table2 break next jump parentjump exit parent return)]
      [(eq? '/ (operator lis)) (list (M_round (get_oa (exec_operator / lis globalTable table table2 break next jump parentjump exit parent return))) (oad (exec_operator / lis globalTable table table2 break next jump parentjump exit parent return)))]
      [(eq? '% (operator lis)) (exec_operator remainder lis globalTable table table2 break next jump parentjump exit parent return)]
      [(eq? 'new (operator lis)) (list (M_construct lis globalTable table table2 break next jump parentjump exit parent return) (list globalTable (list table table2)))]
      [else (error "bad operator")]
      )))

(define exec_operator
  (lambda (opt lis globalTable table table2 break next jump parentjump exit parent return)
    (list (opt (getInnerValue (M_value (expression1 lis) globalTable table table2 break next jump parentjump exit parent return)) (getInnerValue (M_value (expression2 lis) (getInnerGlobalTable (M_value (expression1 lis) globalTable table table2 break next jump parentjump exit parent return)) (getInnerVarTable (M_value (expression1 lis) globalTable table table2 break next jump parentjump exit parent return)) (getInnerVarTable2 (M_value (expression1 lis) globalTable table table2 break next jump parentjump exit parent return)) break next jump parentjump exit parent return)))
          (getInnerWholeTable (M_value (expression2 lis) (getInnerGlobalTable (M_value (expression1 lis) globalTable table table2 break next jump parentjump exit parent return)) (getInnerVarTable (M_value (expression1 lis) globalTable table table2 break next jump parentjump exit parent return)) (getInnerVarTable2 (M_value (expression1 lis) globalTable table table2 break next jump parentjump exit parent return)) break next jump parentjump exit parent return)) )))

(define exec_bool_operator
  (lambda (opt lis globalTable table table2 break next jump parentjump exit parent return)
    (list (opt (getInnerValue (M_boolean (expression1 lis) globalTable table table2 break next jump parentjump exit parent return)) (getInnerValue (M_boolean (expression2 lis) (getInnerGlobalTable (M_boolean (expression1 lis) globalTable table table2 break next jump parentjump exit parent return)) (getInnerVarTable (M_boolean (expression1 lis) globalTable table table2 break next jump parentjump exit parent return)) (getInnerVarTable2 (M_boolean (expression1 lis) globalTable table table2 break next jump parentjump exit parent return)) break next jump parentjump exit parent return)))
          (getInnerWholeTable (M_boolean (expression2 lis) (getInnerGlobalTable (M_boolean (expression1 lis) globalTable table table2 break next jump parentjump exit parent return)) (getInnerVarTable (M_boolean (expression1 lis) globalTable table table2 break next jump parentjump exit parent return)) (getInnerVarTable2 (M_boolean (expression1 lis) globalTable table table2 break next jump parentjump exit parent return)) break next jump parentjump exit parent return)) )))

;boolean state
;takes a list or element and a table as input
;return the boolean result after execting all commands
(define M_boolean
  (lambda (lis globalTable table table2 break next jump parentjump exit parent return)
    (cond
      [(null? lis) #f]
      ;if the element is "true", return #t
      [(and (not (list? lis)) (eq? lis 'true)) (list #t (list globalTable (list table table2)))]
      ;if the element is "false", return #f
      [(and (not (list? lis)) (eq? lis 'false)) (list #f (list globalTable (list table table2)))]
      ;if the element is not a list and not "true" or "false", meaning that it is a var name
      ;return its value from the binding table
      [(not (list? lis)) (list (getBinding table lis) (list globalTable (list table table2)))]
      ;operations
      [(eq? 'funcall (operator lis)) (M_value lis globalTable table table2 break next jump parentjump exit parent return)]
      [(eq? '> (operator lis)) (exec_operator > lis globalTable table table2 break next jump parentjump exit parent return)]
      [(eq? '< (operator lis)) (exec_operator < lis globalTable table table2 break next jump parentjump exit parent return)]
      [(eq? '>= (operator lis)) (exec_operator >= lis globalTable table table2 break next jump parentjump exit parent return)]
      [(eq? '<= (operator lis)) (exec_operator <= lis globalTable table table2 break next jump parentjump exit parent return)]
      [(eq? '== (operator lis)) (exec_operator eq? lis globalTable table table2 break next jump parentjump exit parent return)]
      [(eq? '!= (operator lis)) (list (not (getInnerValue (exec_operator eq? lis globalTable table table2 break next jump parentjump exit parent return))) (getInnerWholeTable (exec_operator > lis globalTable table table2 break next jump parentjump exit parent return)))]
      [(eq? '&& (operator lis)) (exec_bool_operator myAnd lis globalTable table table2 break next jump parentjump exit parent return)]
      [(eq? '|| (operator lis)) (exec_bool_operator myOr lis globalTable table table2 break next jump parentjump exit parent return)]
      [(eq? '! (operator lis)) (list (not (getInnerValue (M_boolean (expression1 lis) globalTable table table2 break next jump parentjump exit parent return))) (getInnerWholeTable (M_boolean (expression1 lis) globalTable table table2 break next jump parentjump exit parent return)))])))

(define myAnd
  (lambda (a b)
    (and a b)))

(define myOr
  (lambda (a b)
    (or a b)))

(define getElseBody
  (lambda (lis)
    (get_oa (get_od (get_od (get_od lis))))))

;if state
(define M_if
  (lambda (lis globalTable table table2 break next jump parentjump exit parent return)
    (cond
      ;if the condition is true, execute statement 1
      [(getInnerValue (M_boolean (expression1 lis) globalTable table table2 break next jump parentjump exit parent return)) (M_state (expression2 lis) (getInnerWholeTable (M_boolean (expression1 lis) globalTable table table2 break next jump parentjump exit parent return)) break next jump parentjump exit parent return)]
      ;otherwise, if there is no else, meaning that no statement 2, return the table without execting anything
      [(null? (get_od (get_od (get_od lis)))) (list globalTable (list table table2))]
      ;execute statement 2
      [else (M_state (getElseBody lis) (list globalTable (list table table2)) break next jump parentjump exit parent return)])))

;while state
(define M_while
  (lambda (lis globalTable table table2 next jump parentjump exit return)
    (call/cc (lambda (break) (M_while_cc lis globalTable table table2 break '() jump parentjump exit return)))))

;while state helper function
(define M_while_cc
  (lambda (lis globalTable table table2 break next jump parentjump exit return)
    (cond
      ;keep executing statement as long as the condition is true
      [(get_oa(M_boolean (get_oa (get_od lis)) globalTable table table2 break next jump parentjump exit 'noparent return))
       (M_while lis globalTable (get_oa (delete_binding (getInnerWholeTable (M_state (get_oa (get_od (get_od lis))) (list globalTable (addNewTableForBoth (getInnerWholeTable (getInnerWholeTable (M_boolean (get_oa (get_od lis)) globalTable table table2 break next jump parentjump exit 'noparent return))))) break next jump parentjump exit lis return))))
                (delete_second (oad (addNewTableForBoth (delete_binding (getInnerWholeTable (M_state (get_oa (get_od (get_od lis))) (getInnerWholeTable (getInnerWholeTable (M_boolean (get_oa (get_od lis)) globalTable table table2 break next jump parentjump exit 'noparent return))) break next jump parentjump exit lis return))))))
                               next jump parentjump exit return)]
      [else (list globalTable (list table table2))])))

(define addNewTableForBoth
  (lambda (table)
    (list (addNewTable (get_oa table)) (addNewTableForFunc (oad table)))))

(define addNewTableForFunc
  (lambda (table)
    (append table '((()())))))

;round a number
;if the number is positive, round it to the largest number that is smaller than it
;if the number is negative, round it to the smallest number that is largest than it
(define M_round
  (lambda (v)
    (if (>= v 0) (M_positive v)
        (M_negative v))))

(define M_positive
  (lambda (v)
    (if (< v 1) 0
        (+ 1 (M_positive (- v 1))))))

(define M_negative
  (lambda (v)
    (if (> v 0) 1
        (- (M_negative (+ v 1)) 1))))

;finally state
(define M_finally
  (lambda (lis globalTable table table2 break next jump parentjump exit parent return)
    (M_overall_cc (oad lis) (list globalTable (list table table2)) break next jump parentjump exit parent return)))

;try state
;assign the next to be the finally section
;move jump to parent and assign catch section to jump
;use call/cc so that after the throw, M_try will be removed from stack
(define M_try
  (lambda (lis globalTable table table2 break next jump parentjump parent return)
    (call/cc (lambda (exit) (M_state (final_sec lis) (M_overall_cc (oad lis) (list globalTable (list table table2)) break (final_sec lis) (caddr lis) jump exit parent return) break next jump parentjump exit parent return)))))


;get the final section in the try section
(define final_sec
  (lambda (lis)
    (get_oa (cddr (get_od lis)))))

;throw state
;delete the last table and add a new table with the exception in it
(define M_throw
  (lambda (lis globalTable table table2 break next jump parentjump exit parent return)
    (if (list? jump)
      (if (null? jump)
          (exit (M_state jump (list globalTable (list (addBinding (deep_adding (deep_deleting (getInnerVarTable (M_value (oad lis) globalTable table table2 break next jump parentjump exit parent return)))) 'eException (get_oa (M_value (oad lis) globalTable table table2 break next jump parentjump exit parent return))) (getInnerVarTable2 (M_value (oad lis) globalTable table table2 break next jump parentjump exit parent return)))) break next parentjump 'nojump exit parent return))
          (exit (M_state jump (list globalTable (list (addBinding (deep_adding (deep_deleting (getInnerVarTable (M_value (oad lis) globalTable table table2 break next jump parentjump exit parent return)))) (get_oa (oad jump)) (get_oa (M_value (oad lis) globalTable table table2 break next jump parentjump exit parent return))) (funcTable (getInnerVarTable2 (oad lis) table table2 break next jump parentjump exit parent return)))) break next parentjump 'nojump exit parent return)))
      (error "Invalid Throw Statement"))))

;catch state
(define M_catch
  (lambda (lis globalTable table table2 break next jump parentjump exit parent return)
    (M_state next (M_overall_cc (caddr lis) (list globalTable (list table table2)) break next jump parentjump exit parent return) break '() jump parentjump exit parent return)))


;get first layer table
(define getFirst
  (lambda (table)
    (if (null? table) 0
        (getSecond (get_oa table)))))

;get second layer table
(define getSecond   ; count second table
  (lambda (table)
    (if (null? table) 0
        (+ (getThird (get_oa table)) (getSecond (get_od table))))))

;get third layer table
(define getThird
  (lambda (table)
    (if (null? table) 0
        (+ (getElement (get_oa table))))))

;get element count
(define getElement
  (lambda (table)
    (if (null? table) 0
        (+ 1 (getElement (get_od table))))))

;make closure for functions
(define makeClosure
  (lambda (lis table table2)
    (append lis (list (list (getFirst table) (+ 1 (getSecond table2)))))))

;modified method: list both table
(define M_function
  (lambda (lis globalTable table table2 break next jump parentjump exit parent return) ; table store var, table2 store fucntion
    (if (eq? (get_oa (get_od lis)) 'mainn) (M_state '(funcall main) (list globalTable (list table (addBinding_helper table2 (get_oa (get_od lis)) (makeClosure (get_od (get_od lis)) table table2)))) break next jump parentjump exit parent return)
        (list globalTable (list table (addBinding_helper table2 (get_oa (get_od lis)) (addThis (makeClosure (get_od (get_od lis)) table table2) globalTable)))))))

(define getClasses
  (lambda (classNameList)
    (if (null? classNameList) 0
        (+ 1 (getClasses (get_od classNameList))))))

(define addThis
  (lambda (closure globalTable)
    (append closure (list (getClasses (get_oa (globalTable)))))))

;create binding var table
(define createBind_var
  (lambda (num table return)
    (cond
      [(eq? 0 num) (return '() 0)]
      [(null? table) (return '() num)]
      [(list? (get_oa (get_oa table))) (createBind_var num (get_oa table) (lambda (v n) (createBind_var n (get_od table) (lambda (v1 n1) (return (cons v v1) n1)))))]
      [else (appendBind_var num (get_oa table) (get_oa (get_od table)) (lambda (v1 v2 n) (return (list v1 v2) n)))])))

;append binding
(define appendBind_var
  (lambda (num table1 table2 return)
    (cond
      [(eq? 0 num) (return '() '() 0)]
      [(null? table1) (return '() '() num)]
      [(appendBind_var (- num 1) (get_od table1) (get_od table2) (lambda (v1 v2 n) (return (cons (get_oa table1) v1) (cons (get_oa table2) v2) n)))])))

;create binding function table
(define createBind_func
  (lambda (num table return)
    (cond
      [(eq? 0 num) (return '() 0)]
      [(null? table) (return '() num)]
      [(null? (get_oa table)) '((() ()))]
      [(list? (get_oa (get_oa table))) (createBind_func num (get_oa table) (lambda (v n) (createBind_func n (get_od table) (lambda (v1 n1) (return (cons v v1) n1)))))]
      [else (appendBind_func num (get_oa table) (get_oa (get_od table)) (lambda (v1 v2 n) (return (list v1 v2) n)))])))

;append binding function table
(define appendBind_func
  (lambda (num table1 table2 return)
    (cond
      [(eq? 0 num) (return '() '() 0)]
      [(null? table1) (return '() '() num)]
      [(appendBind_func (- num 1) (get_od table1) (get_od table2) (lambda (v1 v2 n) (return (cons (get_oa table1) v1) (cons (get_oa table2) v2) n)))])))

;get number of active second layer of vars
(define getActive_var
  (lambda (lis table)
    (createBind_var (get_oa (get_oa (get_od (get_od lis)))) table (lambda (v n) v))))

;get number of active functions
(define getActive_fun
  (lambda (lis table2)
    (createBind_func (get_oa (get_od (get_oa (get_od (get_od lis))))) table2 (lambda (v n) v))))

;closure in form (param body activepart)
(define getClosure
  (lambda (name table2)
    (if (contains_helper table2 name) (getBinding_helper table2 name)
        'no)))
        ;(error "function not defined"))))

;bind actual parameters and formal parameters
(define bindParam
  (lambda (actualparam formalparam currenttable table2 closuretable globalTable)
    (cond
      [(and (null? actualparam) (null? formalparam)) closuretable]
      [(null? formalparam) (error "param list does not match")]
      [(null? actualparam) (error "param list does not match")]
      [else (bindParam (get_od actualparam) (get_od formalparam) currenttable table2 (addBinding closuretable (get_oa formalparam) (cond
                                                                                                                     [(number? (get_oa actualparam)) (get_oa actualparam)]
                                                                                                                     [(eq? (get_oa actualparam) 'true) #t]
                                                                                                                     [(eq? (get_oa actualparam) 'false) #f]
                                                                                                                     [else (get_oa (M_value (get_oa actualparam) globalTable currenttable table2 'nobreak 'nonext 'nojump 'noparentjump 'noexit 'noparent 'noreturn))])) globalTable)])))


;function call
(define funcall_v
  (lambda (lis globalTable table table2 exit jump)
    (M_funcall lis globalTable table table2 'nobreak '() jump 'noparentjump exit 'noparent 'noreturn)))
           
(define M_funcall ; always return '(result ((table1 (table2)))) or (((table1) (table2)))
  (lambda (lis globalTable table table2 break next jump parentjump exit parent return)
    (if (eq? (get_oa (get_od lis)) 'mainmn) (return (if (list? (get_oa (funcexe lis globalTable table table2 break next jump parentjump exit parent return))) 'Noreturn
                                            (cond
                                              [(eq? #t (get_oa (funcexe lis globalTable table table2 break next jump parentjump exit parent return))) 'true]
                                              [(eq? #f (get_oa (funcexe lis globalTable table table2 break next jump parentjump exit parent return))) 'false]
                                              [else (get_oa (funcexe lis globalTable table table2 break next jump parentjump exit parent return))])))
        (if (list? (get_oa (funcexe lis globalTable table table2 break next jump parentjump exit parent return)))
            (list globalTable (update_table_both (list (updateThis table (oad (funcexe lis globalTable table table2 break next jump parentjump exit parent return)) (getInsCall_v (oad lis) globalTable table table2)) table2) (delete_both (oad (funcexe lis globalTable table table2 break next jump parentjump exit parent return)))))
            (list (get_oa (funcexe lis globalTable table table2 break next jump parentjump exit parent return))
                  (list globalTable (update_table_both (list (updateThis table (oad (getInnerWholeTable (funcexe lis globalTable table table2 break next jump parentjump exit parent return))) (getInsCall_v (oad lis) globalTable table table2)) table2) (delete_both (oad (getInnerWholeTable (funcexe lis globalTable table table2 break next jump parentjump exit parent return)))))))))))

(define getInsCall_v
  (lambda (lis globalTable table table2)
    (cond
      [(not (list? lis)) 'this]
      [(eq? 'this (oad lis)) 'this]
      [(eq? 'super (oad lis)) 'this]
      [else (oad lis)])))

(define updateThis_var
  (lambda (oldVarTable var-table insOn)
    (modify_binding oldVarTable insOn (getBinding var-table 'this))))
     
(define updateThis
  (lambda (oldVarTable var-func-table insOn)
    (if (null? (caaar oldVarTable)) oldVarTable
        (updateThis_var oldVarTable (get_oa var-func-table) insOn))))

(define getFuncClosure
  (lambda (lis globalTable table table2)
    (cond
      [(not (list? lis))
       (cond
         [(list? (getClosure lis table2)) (getClosure lis table2)]
         [else (decideDot_func (cons 'dot (list 'this lis)) globalTable table table2)])]
       [else (decideDot_func lis globalTable table table2)])))


;function execution
(define funcexe
  (lambda (lis globalTable table table2 break next jump parentjump exit parent return)
    (if (null? (get_od (get_od lis)))
        (M_overall (oad (getFuncClosure (oad lis) globalTable table table2)) ;fun closure then (cadr body)
               (list globalTable (list (bindParam_class '() (get_oa (getFuncClosure (oad lis) globalTable table table2)) table table2 (addNewTable (getActive_var (getFuncClosure (oad lis) globalTable table table2) table)) globalTable (getInsCall (oad lis) globalTable table table2))
               (addNewTable_func (getActive_fun (getFuncClosure (oad lis) globalTable table table2) table2))))
               break next jump parentjump exit parent)
    (M_overall (oad (getFuncClosure (oad lis) globalTable table table2))
               (list globalTable (list (bindParam_class (get_od (get_od lis)) (get_oa (getFuncClosure (oad lis) globalTable table table2)) table table2 (addNewTable (getActive_var (getFuncClosure (oad lis) globalTable table table2) table)) globalTable (getInsCall (oad lis) globalTable table table2))
               (addNewTable_func (getActive_fun (getFuncClosure (oad lis) globalTable table table2) table2))))
               break next jump parentjump exit parent))))

; (dot (new C) m)
(define getInsCall
  (lambda (lis globalTable table table2)
    (cond
      [(not (list? lis)) (getBinding table 'this)]
      [(eq? 'this (oad lis)) (getBinding table 'this)]
      [(eq? 'super (oad lis)) (getBinding table 'this)]
      [else
       (cond
         [(list? (oad lis))
          (cond
            [(eq? (get_oa (oad lis)) 'new) (get_oa (M_value (oad lis) globalTable table table2 'break 'next 'jump 'parentjump 'exit 'parent 'return))]
            [else (get_oa (M_value (oad lis) globalTable table table2 'break 'next 'jump 'parentjump 'exit 'parent 'return))])]
          [else (getBinding table (oad lis))])])))
            

(define bindParam_class
  (lambda (actualparam formalparam currenttable table2 closuretable globalTable insOn)
    (addBinding (bindParam actualparam formalparam currenttable table2 closuretable globalTable) 'this insOn))) 
    
;update both var table and function table
(define update_table_both
  (lambda (prelis newlis)
    (if (null? newlis) prelis
        (cons (update_table_first (get_oa prelis) (get_oa newlis)) (get_od prelis)))))

(define update_table_first
  (lambda (old new)
    (cond
      [(null? new) old]
      [else (cons (update_table_second (get_oa old) (get_oa new)) (update_table_first (get_od old) (get_od new)))])))

(define update_table_second
  (lambda (old new)
    (if (null? new) old
        (update_table_second (update_table_third old (get_oa new)) (get_od new)))))

(define update_table_third
  (lambda (old new)
    (cond
      [(null? new) old]
      [(null? (get_oa new)) old]
      [(update old (get_oa new) (oad new))])))

(define update
  (lambda (old newvar newval)
    (if (null? newvar) old
        (update (modify_binding_helper old (get_oa newvar) (get_oa newval)) (get_od newvar) (get_od newval)))))

(define delete_both
  (lambda (lis) ;contains (table table2)
    (cond
      [(null? lis) '()]
      [else (list (delete_second (get_oa lis)) (delete_second (oad lis)))])))

(define delete_second
  (lambda (table)
    (cond
      [(null? table) '()]
      [(null? (get_od table)) '()]
      [else (cons (get_oa table) (delete_second (get_od table)))])))


;--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
;--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

(define makeClosureClassFunction
  (lambda (lis)
    (append lis (list (list '0 (+ 1 '0))))))

(define addClassFieldAndMethod
  (lambda (lis classClosure)
    (cond
      [(null? lis) classClosure]
      [(eq? 'var (get_oa (get_oa lis))) (addClassFieldAndMethod (get_od lis) (addField (get_od (get_oa lis)) classClosure))] ; '(x 5)
      [else (addClassFieldAndMethod (get_od lis) (addFunction (get_oa lis) classClosure))])))

(define getDefaultField
  (lambda (lis)
    (if (null? (get_od lis)) (append lis (list '0))
        lis)))

(define addField
  (lambda (lis classClosure)
    (cons (get_oa classClosure) (cons (addBinding_inner (oad classClosure) (get_oa (getDefaultField lis)) (oad (getDefaultField lis))) (cddr classClosure)))))

(define addFunction
  (lambda (lis classClosure)
    (cons (get_oa classClosure) (cons (oad classClosure) (list (addBinding_inner (oadd classClosure) (oad lis) (makeClosureClassFunction (cddr lis))))))))

(define addSuperClass
  (lambda (lis classClosure)
    (if (null? (oadd lis)) (cons (get_oa classClosure) (get_od classClosure))
        (cons (cons (oad (oadd lis)) (get_oa classClosure)) (get_od classClosure)))))

(define addSuperField
  (lambda (globalTable classClosure)
    (if (null? (get_oa classClosure)) classClosure
        (cons (get_oa classClosure)
          (cons (list (append (caadr classClosure) (caadr (getBinding_inner globalTable (caar classClosure))))
                (append (cadadr classClosure) (cadadr (getBinding_inner globalTable (caar classClosure)))))
                                   (cddr classClosure))))))
    

(define addSuperMethod
  (lambda (globalTable classClosure)
    (if (null? (get_oa classClosure)) classClosure
        (cons (get_oa classClosure)
          (cons (oad classClosure)
                (list (list (append (caaddr classClosure) (caaddr (getBinding_inner globalTable (caar classClosure))))
                (append (oad (oadd classClosure)) (oad (oadd (getBinding_inner globalTable (caar classClosure))))))))))))

(define createClassClosure
  (lambda (globalTable lis)
    (addSuperMethod globalTable (addSuperField globalTable (addClassFieldAndMethod (cadddr lis) (addSuperClass lis '(() (() ()) (() ()))))))))
    

; create class
; globaltable ((classname1, classname2 ) (((superclass) ((ins field) (default ins field)) ((methods) (method closure))), classclosure2))
; globaltable ((classname1, classname2 ) (((superclass) ((ins field) (default ins field)) ((methods) (closres))), classclosure2))

(define M_class
  (lambda (lis globalTable table table2 break next jump parentjump exit parent return)
    (list (addBinding_inner globalTable (oad lis) (createClassClosure globalTable lis)) (list table table2))))

(define initIns
  (lambda (lis_value globalTable table table2 exit)
    (if (null? lis_value) '()
        (append (initIns (get_od lis_value) globalTable table table2 exit) (list (get_oa (M_value (get_oa lis_value) globalTable table table2 'nobreak 'nonext 'nojump 'noparentjump exit 'noparent 'noreturn)))))))

; ins closure : ((runtime type) (class) (in field value))           
(define createInsClosure
  (lambda (lis globalTable table table2 exit)
    (if (contains_inner globalTable (oad lis)) (cons (oad lis) (cons (getBinding_inner globalTable (oad lis)) (list (initIns (cadadr (getBinding_inner globalTable (cadr lis))) globalTable table table2 exit))))
        "No such class Exception")))

; new class()                                                                        
(define M_construct
  (lambda (lis globalTable table table2 break next jump parentjump exit parent return)
    (createInsClosure lis globalTable table table2 exit)))

(define countIndex
  (lambda (lis)
    (if (null? lis) 0
        (+ 1 (countIndex (get_od lis))))))

(define getFirstBindingVar_3
  (lambda (var varlist)
    (cond
      [(null? varlist) (error "No such var")]
      [(eq? var (get_oa varlist)) (countIndex (get_od varlist))]
      [else (getFirstBindingVar_3 var (get_od varlist))])))

(define getFirstBindingValue_3
  (lambda (valuelist index)
    (cond
      [(eq? 0 index) (get_oa valuelist)]
      [else (getFirstBindingValue_3 (get_od valuelist) (- index 1))])))


; takes '(dot a x) or (dot this x) or (x) or (dot super x)
(define decideDot_var
  (lambda (lis globalTable table table2)
    (cond                
      [(eq? 'this (oad lis)) (getFirstBindingValue_3 (oadd (getBinding table 'this)) (getFirstBindingVar_3 (oadd lis) (caadr (oad (getBinding table 'this)))))] ; (caddr lis) is 'x
      [(eq? 'super (oad lis)) (getFirstBindingValue_3 (oadd (getBinding table 'this))  ; caadr get var lis of super class
                                                       (getFirstBindingVar_3 (oadd lis) (caadr (getBinding_inner globalTable (caar (oad (getBinding table 'this)))))))]
      ;[(eq? 'funcall (cadr lis)) funcall
      ; a.x
      [else
       (cond
         [(getFirstBindingValue_3 (oadd (get_oa (M_value (oad lis) globalTable table table2 'break 'next 'jump 'parentjump 'exit 'parent 'return)))
                                  (getFirstBindingVar_3 (oadd lis) (caadr (oad (get_oa (M_value (oad lis) globalTable table table2 'break 'next 'jump 'parentjump 'exit 'parent 'return))))))]
         [else (getFirstBindingValue_3 (oadd (getBinding table (oad lis))) (getFirstBindingVar_3 (oadd lis) (caadr (oad (getBinding table (oad lis))))))])])))

; return func closure
(define getFirstBindingFunc_3
  (lambda (var varlist closurelist)
    (cond
      [(null? varlist) (error "No such func")]
      [(eq? var (get_oa varlist)) (get_oa closurelist)]
      [else (getFirstBindingFunc_3 var (get_od varlist) (get_od closurelist))])))

(define getMethod_Name_ListFromClassClosure
  (lambda (lis)  ;lis is class closure
    (get_oa (oadd lis))))

(define getMethod_Closure_ListFromClassClosure
  (lambda (lis)  ;lis is class closure
    (oad (oadd lis))))

;(funcall (dot super m))
;pass in (dot super m)
;(dot (new A) x)
(define decideDot_func
  (lambda (lis globalTable table table2)
    (cond                                                       
      [(eq? 'this (oad lis))
       (getFirstBindingFunc_3 (oadd lis) (getMethod_Name_ListFromClassClosure (oad (getBinding table 'this))) (getMethod_Closure_ListFromClassClosure (oad (getBinding table 'this))))] ; (caddr lis) is 'm
      [(eq? 'super (oad lis))
       (getFirstBindingFunc_3 (oadd lis) (getMethod_Name_ListFromClassClosure (getBinding_inner globalTable (caar (oad (getBinding table 'this)))))
                                          (getMethod_Closure_ListFromClassClosure (getBinding_inner globalTable (caar (oad (getBinding table 'this))))))]
      ;[(eq? 'funcall (cadr lis)) funcall
      ; a.x
      [else
       (cond
         [(list? (oad lis)) (getFirstBindingFunc_3 (oadd lis) (getMethod_Name_ListFromClassClosure (oad (get_oa (M_value (oad lis) globalTable table table2 'break 'next 'jump 'parentjump 'exit 'parent 'return))))
                                                    (getMethod_Closure_ListFromClassClosure (oad (get_oa (M_value (oad lis) globalTable table table2 'break 'next 'jump 'parentjump 'exit 'parent 'return)))))]
         [else (getFirstBindingFunc_3 (oadd lis) (getMethod_Name_ListFromClassClosure (oad (getBinding table (oad lis))))
                                      (getMethod_Closure_ListFromClassClosure (oad (getBinding table (oad lis)))))])])))

(define oadd
  (lambda (lis)
    (caddr lis)))

(define oad
  (lambda (lis)
    (cadr lis)))

(define get_oa
  (lambda (lis)
    (car lis)))

(define get_od
  (lambda (lis)
    (cdr lis)))

(define p
  (lambda (interesting-val)
    (println "here's an interesting val:") 
    (println interesting-val) ; statement to insert
    ))
      





