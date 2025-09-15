; Options: -v 0 --produce-models --lang smt2
(declare-fun start!1 () Bool)

(assert start!1)

(declare-fun fahrenheit!1 () (_ FloatingPoint 11 53))

(assert (=> start!1 false))

(assert (=> start!1 true))

(check-sat)


