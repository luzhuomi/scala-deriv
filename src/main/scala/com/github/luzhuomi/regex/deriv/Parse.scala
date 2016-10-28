package com.github.luzhuomi.regex.deriv

import com.github.luzhuomi.scalazparsec.NonBacktracking._
import com.github.luzhuomi.regex.pderiv.{ RE => PD, Common => PC }
import com.github.luzhuomi.regex.deriv.{ RE => D, Common => C }
import com.github.luzhuomi.regex.pderiv.ExtPattern._
import com.github.luzhuomi.regex.pderiv.IntPattern._
import com.github.luzhuomi.regex.pderiv.Parser._
import com.github.luzhuomi.regex.pderiv.Translate._

object Parse {


	def coerce(r:PD.RE):D.RE = r match 
	{
		case PD.Phi              => D.Phi
		case PD.Empty            => D.Eps
		case PD.L(c)             => D.L(c)
		case PD.Seq(r1,r2)       => D.Seq(coerce(r1),coerce(r2))
		case PD.Choice(r1,r2,gf) => D.Choice(List(coerce(r1),coerce(r2)),coerce(gf))
		case PD.Star(r,gf)       => D.Star(coerce(r),coerce(gf))
		case PD.Any              => D.Any
		case PD.Not(cs)          => D.Not(cs.toSet)
	}

	def coerce(gf:PC.GFlag):C.GFlag = gf match 
	{
		case PC.Greedy    => C.Greedy
		case PC.NotGreedy => C.NotGreedy
	}


	def parse(regex:String):Option[D.RE] = 
	{
		parseEPat(regex) match 
		{
			case Consumed(Some((ep,Nil))) => 
			{
				val ip = translate(ep)
				val r = strip(ip)
				Some(coerce(r))
			} 
			case _ => None // compilation fail
		}
	}


}

