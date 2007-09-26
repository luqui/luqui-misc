package com.learningrx.AttentionArrows
{
	import flash.display.Sprite;
	import flash.geom.ColorTransform;
	import flash.filters.*;	
	import flash.text.*;
	
	import com.learningrx.*

	public class Countdown extends Sprite
	{
		private var _Parent:Game;
		private var _Number:Number;
		private var _Color:Number;
		private var _Height:Number = 200;
		private var _TextField:TextField;
		private var _Fading:String;
		
		public function Countdown(pParent:Game)
		{
			_Parent = pParent;
			CreateTextField();
			AddFilters();
		}
		
	}
}