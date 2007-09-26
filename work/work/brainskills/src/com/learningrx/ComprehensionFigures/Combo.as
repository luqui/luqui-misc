package com.learningrx.ComprehensionFigures
{
	import com.learningrx.Utilities;
	import com.learningrx.ComprehensionFigures.Figure;
	
	public class Combo extends Figure
	{
		private var _distanceBetween:Number = 16;
		private var _distanceOverlap:Number = -4 * _distanceBetween;
		private var _distanceTouching:Number = -1;
		private var _insidePercentage:Number = .6;

		private var _figure1:Figure;
		private var _figure2:Figure;
		private var _position:String;
		
		public function Combo(pFigure1:Figure, 
									 pFigure2:Figure,
									 pPosition:String)
		{
			super("combo");
			_figure1 = pFigure1;
			_figure2 = pFigure2;
			addChild(_figure1);
			addChild(_figure2);
			Draw(pPosition);
		}
		
		override public function Highlight():void
		{
			_figure1.Highlight();
			_figure2.Highlight();
		}
		
		override public function Unhighlight():void
		{
			_figure1.Unhighlight();
			_figure2.Unhighlight();
		}
		
		override public function Clicklight(pRightAnswer:Boolean):void
		{
			_figure1.Clicklight(pRightAnswer);
			_figure2.Clicklight(pRightAnswer);
		}
		
		override public function ShowFill():void
		{
			if (_figure1.type != 'combo')
			{
				_figure1.ShowFill();
			}
			if (_figure2.type != 'combo')
			{
				_figure2.ShowFill();
			}
		}

		override public function HideFill():void
		{
			if (_figure1.type != 'combo')
			{
				_figure1.HideFill();
			}
			if (_figure2.type != 'combo')
			{
				_figure2.HideFill();
			}
		}

// -------------------------------------------------------------------

		private function Draw(pPosition:String):void
		{
			switch(pPosition)
			{
				case 'Above':
					PutAbove('noOverlap');
					break;
				case 'Below':
					PutBelow('noOverlap');
					break;
				case 'Inside':
					PutInside();
					break;
				case 'Around':
					PutAround();
					break;
				case 'Left':
					PutLeft('noOverlap');
					break;
				case 'Right':
					PutRight('noOverlap');
					break;
				case 'Between':
					PutBetween();
					break;
				case 'Higher':
					PutHigher('noOverlap');
					break;
				case 'Lower':
					PutLower('noOverlap');
					break;
				case 'Overlapping':
					PutOverlapping();
					break;
				case 'Touching':
					PutTouching();
					break;
				case 'Intersecting':
					PutIntersecting();
					break;
				case 'Behind':
					PutBehind();
					break;
				case 'InFrontOf':
					PutInFrontOf();
					break;
			}
			if ('Overlapping' == pPosition || 'Behind' == pPosition || 'InFrontOf' == pPosition)
			{
				this.ShowFill();
			}
			else
			{
				this.HideFill();
			}
		}
		
		private function PutAbove(pOverlap:String):void
		{
			var tDistance:Number;
			switch (pOverlap)
			{
				case 'overlap':
					tDistance = _distanceOverlap;
					break;
				case 'noOverlap':
					tDistance = _distanceBetween;
					break;
				case 'touching':
					tDistance = _distanceTouching;
					break;
			}
			_figure2.y = _figure1.height + tDistance;
			CenterFiguresHorizontally();
		}

		private function PutInside():void
		{
			if (_figure1.width > _figure1.height)
			{
				_figure1.height = _figure1.height * (_insidePercentage * _figure2.width) / _figure1.width;
				_figure1.width = _insidePercentage * _figure2.width;
			}
			else
			{
				_figure1.width = _figure1.width * (_insidePercentage * _figure2.height) / _figure1.height;
				_figure1.height = _insidePercentage * _figure2.height;
			}
			CenterFiguresHorizontally();
			CenterFiguresVertically();
		}
		
		private function PutLeft(pOverlap:String):void
		{
			var tDistance:Number;
			switch (pOverlap)
			{
				case 'overlap':
					tDistance = _distanceOverlap;
					break;
				case 'noOverlap':
					tDistance = _distanceBetween;
					break;
				case 'touching':
					tDistance = _distanceTouching;
					break;
			}
			_figure2.x = _figure1.x + _figure1.width + tDistance;
			CenterFiguresVertically();
		}
		
		private function PutHigher(pOverlap:String):void
		{
			var tDistance:Number;
			switch (pOverlap)
			{
				case 'overlap':
					tDistance = _distanceOverlap;
					_figure2.y = _figure1.y + _figure1.height + _distanceOverlap;
					break;
				case 'noOverlap':
					tDistance = _distanceBetween;
					_figure2.y = _figure1.y - _distanceOverlap;
					break;
			}
			switch (Utilities.RandRange(1, 2))
			{
				case 1:
					_figure2.x = _figure1.width + tDistance;
					break;
				case 2:
					_figure1.x = _figure2.width + tDistance;
					break;
			}
		}
		
		private function PutBelow(pOverlap:String):void
		{
			SwapFigures();
			PutAbove(pOverlap);
		}
		
		private function PutAround():void
		{
			SwapFigures();
			PutInside();
		}
		
		private function PutRight(pOverlap:String):void
		{
			SwapFigures();
			PutLeft(pOverlap);
		}
		
		private function PutBetween():void
		{
			//PutLeft(_figure21, PutRight(_figure21, _figure1, pDistanceBetween), pDistanceBetween);
		}
		
		private function PutLower(pOverlap:String):void
		{
			SwapFigures();
			PutHigher(pOverlap);
		}
		
		private function PutIntersecting():void
		{
			var tDistance:Number;
			switch (Utilities.RandRange(1, 8))
			{
				case 1:
					PutAbove('overlap');
					break;
				case 2:
					PutBelow('overlap');
					break;
				case 3:
					PutLeft('overlap');
					break;
				case 4:
					PutRight('overlap');
					break;
				case 5:
				case 6:
					PutHigher('overlap');
					break;
				case 7:
				case 8:
					PutLower('overlap');
					break;
			}
		}

		private function PutTouching():void
		{
			switch (Utilities.RandRange(1, 4))
			{
				case 1:
					PutAbove('touching');
					break;
				case 2:
					PutBelow('touching');
					break;
				case 3:
					PutLeft('touching');
					break;
				case 4:
					PutRight('touching');
					break;
			}
		}
		
		private function PutOverlapping():void
		{
			switch (Utilities.RandRange(1, 2))
			{
				case 1:
					PutBehind();
					break;
				case 2:
					PutInFrontOf();
					break;
			}
		}
		
		private function PutBehind():void
		{
			PutIntersecting();
		}
		
		private function PutInFrontOf():void
		{
			SwapDepths();
			PutBehind();
		}
		
		private function CenterFiguresHorizontally():void
		{
			if (_figure2.width > _figure1.width)
			{
				_figure1.x = _figure2.x + (_figure2.width - _figure1.width) / 2;
			}
			else
			{
				_figure2.x = _figure1.x + (_figure1.width - _figure2.width) / 2;
			}
		}

		private function CenterFiguresVertically():void
		{
			if (_figure2.height > _figure1.height)
			{
				_figure1.y = _figure2.y + (_figure2.height - _figure1.height) / 2;
			}
			else
			{
				_figure2.y = _figure1.y + (_figure1.height - _figure2.height) / 2;
			}
		}

		private function SwapFigures():void
		{
			var tempFigure:Figure = _figure2;
			_figure2 = _figure1;
			_figure1 = tempFigure;
		}
		
		private function SwapDepths():void
		{
			this.swapChildren(_figure1, _figure2);
		}
	}
}