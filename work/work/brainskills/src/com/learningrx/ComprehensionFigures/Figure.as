package com.learningrx.ComprehensionFigures
{
	import flash.display.Sprite;

	public class Figure extends Sprite
	{
		private var _type:String;
		
		public function Figure(pType:String)
		{
			_type = pType;
		}
		
		public function get type():String
		{
			return _type;
		}
		
		public function set type(pType:String):void
		{
			_type = pType;
		}
		
		public function ShowFill():void
		{
			//_fillMC.alpha = 100;
		}
		
		public function HideFill():void
		{
			//_fillMC.alpha = 0;
		}
		public function Highlight():void
		{
			//_figure1.Highlight();
			//_figure2.Highlight();
		}
		
		public function Unhighlight():void
		{
			//_figure1.Unhighlight();
			//_figure2.Unhighlight();
		}
		
		public function Clicklight(pRightAnswer:Boolean):void
		{
			//_figure1.Clicklight(pRightAnswer);
			//_figure2.Clicklight(pRightAnswer);
		}
		
	}
}