package com.learningrx.ComprehensionFigures
{
	import flash.events.MouseEvent;
	import flash.filters.DropShadowFilter;
	import flash.filters.BitmapFilterQuality;
	import flash.filters.BitmapFilterType;	

	import com.learningrx.*;
	import com.learningrx.Screens.*;
	
	public class AnswerBox extends BasicButton
	{
		private var _RightAnswerFillingColor:Number = 0x00FF00;
		private var _WrongAnswerFillingColor:Number = 0xFF0000;
		private var _InsidePercentage:Number = .8;
		private var _Figure:Figure = new Figure('empty');
		
		public function AnswerBox(pParent:ComprehensionFigures)
		{
			super(pParent);
			_Width = 273;
			_Height = 200;
			_UnhighlightedFillingColor = 0x1E4770;
			_HighlightedFillingColor = 0x009999;
			_LineColor = 0xCCCCCC;
			_LineThickness = 4;
			_CornerRadius = 24;
			AddFilter();
			super.Init();
		}
		
		public function Draw(pFigures:Array,
									pPositions:Array):void
		{
			//trace('Draw', pFigures, pPositions);
			InitFiguresAndPositions(pFigures, pPositions);
			if (this.mouseX >= 0 && this.mouseX <= this.width && this.mouseY >= 0 && this.mouseY <= this.height)
			{
				Highlight();
			}
			else
			{
				Unhighlight();
			}
		}
		
		override public function Highlight():void
		{
			super.Highlight();
			_Figure.Highlight();
		}
		
		override public function Unhighlight():void
		{
			super.Unhighlight();
			_Figure.Unhighlight();
		}
		
		public function Clicklight(pRightAnswer:Boolean):void
		{
			if (pRightAnswer)
			{
				DrawFill(_RightAnswerFillingColor);
			}
			else
			{
				DrawFill(_WrongAnswerFillingColor);
			}
			_Figure.Clicklight(pRightAnswer);
		}
		
		override protected function DoClick():void 
		{
			super.DoClick();
			_Parent.AnswerBoxClicked(this);
		}
		
		private function AddFilter():void
		{
			var dropShadow:DropShadowFilter = new DropShadowFilter();
			dropShadow.distance = 5;
			dropShadow.color = 0x000000;
			dropShadow.angle = 45;
			dropShadow.alpha = .5;
			dropShadow.blurX = 5;
			dropShadow.blurY = 5;
			dropShadow.quality = BitmapFilterQuality.HIGH;
			dropShadow.knockout = false;
			this.filters = [dropShadow];
		}

		private function InitFiguresAndPositions(pFigures:Array,
															  pPositions:Array):void
		{
			var combo1:Combo = new Combo(GetNewFigure(pFigures[0].Name), 
												  GetNewFigure(pFigures[1].Name), 
												  pPositions[0].FunctionName);
			if (pFigures.length == 2)
			{
				AddFigure(combo1);
			}
			else
			{
				var combo2:Combo = new Combo(combo1, GetNewFigure(pFigures[2].Name), 
													  pPositions[1].FunctionName);
				if (pFigures.length == 3)
				{
					AddFigure(combo2);
				}
				else
				{
					AddFigure(new Combo(combo2, GetNewFigure(pFigures[3].Name), 
																		  pPositions[2].FunctionName));
				}
			}
		}
		
		private function GetNewFigure(pName:String):Figure
		{
			if (Turns.IsFigureAShape(pName))
			{
				return new CFShape(pName);
			}
			else
			{
				return new CFObject(pName);
			}
			return null;
		}
		
		private function AddFigure(pFigure:Figure):void
		{
			if (_Figure.type != 'empty')
			{
				this.removeChild(_Figure);
			}
			_Figure = pFigure;
			Utilities.AddChildToDisplayList(this, _Figure);
			ResizeFigure();
		}
		
		private function ResizeFigure():void
		{
			var figureRatio:Number = _Figure.width / _Figure.height;
			var insideHeight:Number = _InsidePercentage * _OutlineMC.height;
			var insideWidth:Number = _InsidePercentage * _OutlineMC.width;
			if (figureRatio > _OutlineMC.width / _OutlineMC.height)
			{
				_Figure.width = insideWidth;
				_Figure.height = _Figure.width / figureRatio;
			}
			else
			{
				_Figure.height = insideHeight;
				_Figure.width = _Figure.height * figureRatio;
			}
			_Figure.x = (_OutlineMC.width - _Figure.width) / 2;
			_Figure.y = (_OutlineMC.height - _Figure.height) / 2;
		}
	}
}