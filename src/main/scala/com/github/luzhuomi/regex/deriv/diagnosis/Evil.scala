package com.github.luzhuomi.regex.deriv.diagnosis

import scala.collection.Map._
import com.github.luzhuomi.regex.deriv.RE._
import com.github.luzhuomi.regex.deriv.Common._
import com.github.luzhuomi.regex.deriv.Parse._
import com.github.luzhuomi.regex.deriv.diagnosis.Ambiguity._
import com.github.luzhuomi.regex.deriv.diagnosis.Universality._

/*
Evil test
Let deriv(sigma*)(r) denotes all derivative descendants of r
strictderiv(sigma*)(r) denotes the non-reflexive descendants.
We say r is evil iff there exists r' in deriv(sigma*)(r) such that
  1) r' is ambiguous and
  2) r' in nrderiv(sigma*)(r') and
  3) there not exits r'' in deriv(sigma*)(r') such that r'' is universal
*/



object Evil 
{
  def strictDeriv(sigma:List[Char], r:RE) : List[RE] = 
    nub(sigma.flatMap(l => allDerivs(sigma,deriv(r,l))))

  def evil(sigma:List[Char], r:RE) : Boolean = {
    val allRp = allDerivs(sigma,r)
    def ambig_loop_no_uni_desc(rp:RE) : Boolean = diagnoseRE(rp) match {
      case Nil => false
      case _::_ => 
	{
	  val allRpp = allDerivs(sigma,rp)
	  val nrds = strictDeriv(sigma,r)
	  (nrds.contains(rp) && allRpp.forall(t=> !(universal(ascii,t))))
	}
    }
    allRp.exists( ambig_loop_no_uni_desc(_))
  }

  def diagnose(src:String):Either[String, Boolean] = parse(src) match {
    case None => Left(s"Unable to parse regex '${src}'. Error: ")
    case Some(pat) => Right(evil(ascii, pat))
  }
}
