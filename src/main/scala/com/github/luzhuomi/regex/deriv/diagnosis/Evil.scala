package com.github.luzhuomi.regex.deriv.diagnosis

import scala.collection.Map._
import com.github.luzhuomi.regex.deriv.RE._
import com.github.luzhuomi.regex.deriv.Common._
import com.github.luzhuomi.regex.deriv.Parse._
import com.github.luzhuomi.regex.deriv.diagnosis.Ambiguity._
import com.github.luzhuomi.regex.deriv.diagnosis.Universality._

/*
Evil test
Let deriv(sigma*)(r) denotes all derivative descandants of r
nrderiv(sigma*)(r) denotes the non-reflexive descandants.
We say r is evil iff there exists r' in deriv(sigma*)(r) such that
  1) r' is ambigous and 
  2) r' in nrderiv(sigma*)(r') and
  3) there not exits r'' in deriv(sigma*)(r') such that r'' is universal
*/



object Evil 
{
}
