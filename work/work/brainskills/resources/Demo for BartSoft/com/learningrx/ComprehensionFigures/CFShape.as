package com.learningrx.ComprehensionFigures
{
	import flash.display.Sprite;
	
	import com.learningrx.*;
	import com.learningrx.ComprehensionFigures.*;

	public class CFShape extends Figure
	{
		public static var Shapes:Array = ['star', 'circle', 'square', 'roundedSquare', 'burst', 'octagon']; //'diamond', 

		private var _SideLength:Number = 100;
		private var _LineThickness:Number = 2;
		private var _LineColor:Number = 0xFFFFFF;
		private var _UnhighlightedFillingColor:Number = 0x1E4770;
		private var _HighlightedFillingColor:Number = 0x009999;
		private var _RightAnswerFillingColor:Number = 0x00FF00;
		private var _WrongAnswerFillingColor:Number = 0xFF0000;
		private var _FillAlpha:Number = 100;
		private var _FillMC:Sprite = new Sprite();
		private var _OutlineMC:Sprite = new Sprite();
		private var _ShapeName:String;
		
		public function CFShape(pShapeName:String)
		{
			super(pShapeName);
			//trace(pShapeName):
			_ShapeName = pShapeName;
			this.addChild(_FillMC);
			this.addChild(_OutlineMC);
			DrawFill(_UnhighlightedFillingColor);
			DrawOutline();
		}
		
		override public function Highlight():void
		{
			DrawFill(_HighlightedFillingColor);
		}
		
		override public function Unhighlight():void
		{
			DrawFill(_UnhighlightedFillingColor);
		}
		
		override public function Clicklight(pRightAnswer:Boolean):void
		{
			if (pRightAnswer)
			{
				DrawFill(_RightAnswerFillingColor);
			}
			else
			{
				DrawFill(_WrongAnswerFillingColor);
			}
		}
		
		override public function ShowFill():void
		{
			//trace('ShowFill');
			_FillMC.alpha = _FillAlpha;
		}
		
		override public function HideFill():void
		{
			//trace('HideFill');
			_FillMC.alpha = 0;
		}
		
//----------------------------

		private function DrawFill(pFillColor:Number):void
		{
			Draw(_FillMC, true, pFillColor, 0);
		}
		
		private function DrawOutline():void
		{
			Draw(_OutlineMC, false, 0, 100);
		}
		
		private function Draw(pDrawObject:Sprite,
									 pSolid:Boolean,
									 pFillColor:Number,
									 pLineAlpha:Number):void
		{
			pDrawObject.graphics.clear();
			pDrawObject.graphics.lineStyle(_LineThickness, _LineColor, pLineAlpha, true, "none", "none", "round");
			if (pSolid)
			{
				pDrawObject.graphics.beginFill(pFillColor, 100);
			}
			switch(_ShapeName.toUpperCase())
			{
				case 'STAR':
					DrawStar(pDrawObject);
					break;
				case 'CIRCLE':
					DrawCircle(pDrawObject);
					break;
				case 'SQUARE':
					DrawSquare(pDrawObject,0);
					break;
				case 'ROUNDED SQUARE':
					DrawSquare(pDrawObject, _SideLength / 2);
					break;
				case 'SUN BURST':
					DrawBurst(pDrawObject);
					break;
				case 'DIAMOND':
					DrawDiamond(pDrawObject);
					break;
				case 'OCTAGON':
					DrawOctagon(pDrawObject);
					break;
			}
			if (pSolid)
			{
				pDrawObject.graphics.endFill();
			}
		}

		private function DrawStar(pDrawObject:Sprite):void
		{
			var tInnerRadius:Number = _SideLength / 2 * .75;
			var step:Number = (Math.PI * 2) / 8;
			pDrawObject.graphics.moveTo(_SideLength, _SideLength / 2);
			for (var i:uint = 1; i <= 8; ++i) 
			{
				pDrawObject.graphics.lineTo(_SideLength / 2 + Math.cos((step * i) - step / 2) * tInnerRadius, 
													 _SideLength / 2 - Math.sin((step * i) - step / 2) * tInnerRadius);
				pDrawObject.graphics.lineTo(_SideLength / 2 + Math.cos((step * i)) * _SideLength / 2, 
													 _SideLength / 2 - Math.sin((step * i)) * _SideLength / 2);
			}
		}

		private function DrawOctagon(pDrawObject:Sprite):void
		{
			var tIndent = Math.round(_SideLength * .2928932188134525);
			pDrawObject.graphics.moveTo(tIndent, 0);
			pDrawObject.graphics.lineTo(_SideLength - tIndent, 0);
			pDrawObject.graphics.lineTo(_SideLength, tIndent);
			pDrawObject.graphics.lineTo(_SideLength, _SideLength - tIndent);
			pDrawObject.graphics.lineTo(_SideLength - tIndent, _SideLength);
			pDrawObject.graphics.lineTo(tIndent, _SideLength);
			pDrawObject.graphics.lineTo(0, _SideLength - tIndent);
			pDrawObject.graphics.lineTo(0, tIndent);
			pDrawObject.graphics.lineTo(tIndent, 0);
		}
		
		
		private function DrawDiamond(pDrawObject:Sprite):void
		{
			pDrawObject.graphics.moveTo(_SideLength / 2, 0);
			pDrawObject.graphics.lineTo(_SideLength, _SideLength / 2);
			pDrawObject.graphics.lineTo(_SideLength / 2, _SideLength);
			pDrawObject.graphics.lineTo(0, _SideLength / 2);
			pDrawObject.graphics.lineTo(_SideLength / 2, 0);
		}
		
		private function DrawBurst(pDrawObject:Sprite):void
		{
			var tInnerRadius:Number = _SideLength / 2 *.75;
			var step:Number = (Math.PI * 2) / 6;
			pDrawObject.graphics.moveTo(_SideLength, _SideLength / 2);
			for (var i:uint = 1; i <= 6; ++i) 
			{
				pDrawObject.graphics.curveTo(_SideLength / 2 + Math.cos((step * i) - (step / 4 * 3))*(tInnerRadius / Math.cos(step / 4)), 
													  _SideLength / 2 - Math.sin((step * i) - (step / 4 * 3))*(tInnerRadius / Math.cos(step / 4)), 
													  _SideLength / 2 + Math.cos((step * i) - step / 2) * _SideLength / 2, 
													  _SideLength / 2 - Math.sin((step * i) - step / 2) * _SideLength / 2);
				pDrawObject.graphics.curveTo(_SideLength / 2 + Math.cos((step * i) - step / 4) * (tInnerRadius / Math.cos(step / 4)), 
													  _SideLength / 2 - Math.sin((step * i) - step / 4) * (tInnerRadius / Math.cos(step / 4)), 
													  _SideLength / 2 + Math.cos((step * i)) * _SideLength / 2, 
													  _SideLength / 2 - Math.sin((step * i)) * _SideLength / 2);
			}
		}

		private function DrawCircle(pDrawObject:Sprite):void
		{
			pDrawObject.graphics.drawCircle(_SideLength / 2, _SideLength / 2, _SideLength / 2);
		}		
		
		private function DrawSquare(pDrawObject:Sprite,
											 pCornerRadius:Number):void
		{
			if (isNaN(pCornerRadius) || pCornerRadius == 0)
			{
				pDrawObject.graphics.drawRect(0, 0, _SideLength, _SideLength);
			}
			else
			{
				pDrawObject.graphics.drawRoundRect(0, 0, _SideLength, _SideLength, pCornerRadius, pCornerRadius);
			}
		}
	}
}