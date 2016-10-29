package com.github.luzhuomi.regex.deriv.diagnosis

import scala.collection.Map._
import com.github.luzhuomi.regex.deriv.RE._
import com.github.luzhuomi.regex.deriv.Common._
import com.github.luzhuomi.regex.deriv.Parse._
import com.github.luzhuomi.regex.deriv.diagnosis.Ambiguity._

object Universality 
{
	def allDerivs(sigma:List[Char],r:RE):List[RE] = 
	{
		def go(sofar:List[RE],rs:List[RE]):List[RE] = rs match 
		{
			case Nil => sofar
			case _   => 
			{
				val rsp = nub(rs.flatMap((r:RE) => 
				{
					for { l <- sigma } yield simp(deriv(r,l))
				}).filter((r:RE) => !sofar.contains(r)))
				go(nub(sofar++rs),rsp)
			}
		}
		go(Nil,List(r))
	}


	def universal(sigma:List[Char],r:RE)(implicit m:PosEps[RE]):Boolean = 
	{
		allDerivs(ascii,r) forall(m.posEps(_))
	}

	val ascii : List[Char] = (0 to 255).map(_.toChar).toList
}