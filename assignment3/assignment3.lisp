(load "~/aima/aima.lisp")
(aima-load 'all)

(setf *australia* '((sa (wa nt q nsw v))
		    (wa (nt sa))
		    (nt (q sa wa))
		    (q (nsw sa nt))
		    (nsw (v sa q))
		    (v (sa nsw))
		    (t)))
 
(setf *colors* '(1 2 3))

    
(defun get-regions (map-representation)
  (map 'list (lambda (m) (nth 0 m)) map-representation))

(defun is-neighbor (state1 state2 map-representation)
  (loop for s in map-representation do 
       (if (eq state1 (nth 0 s)) (return-from is-neighbor (member state2 (nth 1 s))))
       (if (eq state2 (nth 0 s)) (return-from is-neighbor (member state1 (nth 1 s)))))
  nil)

(defun make-map-constraint-fn (map-representation)
  (lambda (var1 val1 var2 val2)
    (not (and
	  (is-neighbor var1 var2 map-representation)
	  (= val1 val2)))))

(defun make-map-coloring-problem (&key (map-representation *australia*) (ncolors 3))
  (make-csp-problem :initial-state (make-csp-state
				    :unassigned (map 'list (lambda (var)
							     (make-csp-var :name var :domain (iota ncolors)))
						     (get-regions map-representation))
				    :assigned nil
				    :constraint-fn (make-map-constraint-fn map-representation))))

