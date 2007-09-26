package com.learningrx.AttentionArrows
{
	import flash.display.Sprite;
	import flash.display.MovieClip;
	import fl.motion.SimpleEase;
	import flash.geom.ColorTransform;
	import flash.geom.Point;
	import flash.filters.BevelFilter;
	import flash.filters.DropShadowFilter;
   import flash.filters.BitmapFilterQuality;
   import flash.filters.BitmapFilterType;	
	import flash.events.TimerEvent;
	import flash.utils.Timer;
	
	import com.learningrx.*;
	
	public class Arrow extends Sprite
	{
		private var _Parent:Game;
		private var _ArrowShape:ArrowShape;
		private var _AltArrows:Object = {red: new AltRedArrow(),
													green: new AltGreenArrow(),
		                                 blue: new AltBlueArrow(), 
													yellow: new AltYellowArrow()};
		private var _CurrentArrow:Sprite;
		private var _Orientation:String;
		private var _Start:Point;
		private var _End:Point;
		private var _Distraction:Boolean = false;
		private var _Moving:Boolean = false;
		private var _Spinning:Boolean = false;
		private var _AnimateTimer:Timer;
		private var _TimerInterval:Number = 60;
		
		public function Arrow(pParent:Game)
		{
			_Parent = pParent;
			_ArrowShape = new ArrowShape();
			_AltArrows = {red: new AltRedArrow(),
							  green: new AltGreenArrow(),
							  blue: new AltBlueArrow(), 
							  yellow: new AltYellowArrow()};
			AddFilters();
		}

		public function Reset(pTurnDetails:Object,
									 pDistraction:Boolean,
									 pSpinning:Boolean)
		{
			this.rotation = Turns.Rotations[pTurnDetails.Orientation];
			SetArrow(pTurnDetails.Color);
			_Start = GetStart(pTurnDetails.Motion, pTurnDetails.Distraction);
			_End = GetEnd(pTurnDetails.Motion, pTurnDetails.Distraction);
			this.x = _Start.x;
			this.y = _Start.y;
			_Distraction = pDistraction;
			_Moving = !(_Start.x == _End.x && _Start.y == _End.y);
			_Spinning = pTurnDetails.Spinning;
			if (_Moving || _Spinning)
			{
				InitAnimateTimer(pTurnDetails.MilliSecondsPerBeat);
				Utilities.StartTimer(_AnimateTimer);
			}
		}

		private function SetArrow(pColor:String):void
		{
			Utilities.RemoveChildFromDisplayList(this, _CurrentArrow);
			if (_Parent.AltArrows)
			{
				_CurrentArrow = _AltArrows[pColor];
			}
			else
			{
				_CurrentArrow = _ArrowShape;
				SetColor(pColor);
			}
			// Arrow registration point needs to be in its center;
			_CurrentArrow.x = -_CurrentArrow.width / 2;
			_CurrentArrow.y = -_CurrentArrow.height / 2;
			Utilities.AddChildToDisplayList(this, _CurrentArrow);
		}

		private function SetColor(pColor:String):void
		{
			var colorInfo:ColorTransform = this.transform.colorTransform;
			colorInfo.color = Turns.GetArrowColorValue(pColor);
			_ArrowShape.transform.colorTransform = colorInfo;
		}

		public function GetPoint(pCurrentCount:Number, 
										 pTotalCount:Number):Point
		{
			var x:Number = SimpleEase.easeQuadPercent(pCurrentCount, _Start.x, _End.x - _Start.x, 
																	pTotalCount, Turns.MOVING_ARROW_EASE_PERCENT);
			var y:Number = SimpleEase.easeQuadPercent(pCurrentCount, _Start.y, _End.y - _Start.y, 
																	pTotalCount, Turns.MOVING_ARROW_EASE_PERCENT);
			return new Point(x, y);
		}

		private function GetEnd(pMotion:String,
										pDistraction:Boolean):Object
		{
			var end:Point;
			switch (pMotion)
			{
				case null:
					end = new Point (_Parent.BackgroundWidth / 2, _Parent.ScoreAndDividerY / 2);
					break;
				case 'left':
					end = new Point (_CurrentArrow.width / 2, _Parent.ScoreAndDividerY / 2);
					break;
				case 'right':
					end = new Point (_Parent.BackgroundWidth - _CurrentArrow.width / 2, _Parent.ScoreAndDividerY / 2);
					break;
				case 'up':
					end = new Point (_Parent.BackgroundWidth / 2, _CurrentArrow.height / 2);
					break;
				case 'down':
					end = new Point (_Parent.BackgroundWidth / 2, _Parent.ScoreAndDividerY - _CurrentArrow.height / 2);
					break;
			}
			if (pDistraction)
			{
				end.x = Utilities.RandRange(end.x / 4, end.x);
				end.y = Utilities.RandRange(end.y / 4, end.y);
			}
			return end;
		}

		private function GetStart(pMotion:String,
										  pDistraction:Boolean):Object
		{
			return GetEnd(Turns.GetOppositeDirection(pMotion), pDistraction);
		}

		private function AddFilters():void
		{
			var bevelFilter:BevelFilter = new BevelFilter();
			bevelFilter.distance = 2;
			bevelFilter.angle = 45;
			bevelFilter.highlightColor = 0xFFFFFF;
			bevelFilter.highlightAlpha = .8;
			bevelFilter.shadowColor = 0x000000;
			bevelFilter.shadowAlpha = .8;
			bevelFilter.blurX = 2;
			bevelFilter.blurY = 2;
			bevelFilter.strength = 1;
			bevelFilter.quality = BitmapFilterQuality.HIGH;
			bevelFilter.type = BitmapFilterType.INNER;
			bevelFilter.knockout = false;
			var dropShadow:DropShadowFilter = new DropShadowFilter();
			dropShadow.distance = 5;
			dropShadow.color = 0x000000;
			dropShadow.angle = 45;
			dropShadow.alpha = .5;
			dropShadow.blurX = 5;
			dropShadow.blurY = 5;
			dropShadow.quality = BitmapFilterQuality.HIGH;
			dropShadow.knockout = false;
			this.filters = [bevelFilter, dropShadow];
		}

		private function OnAnimateTimer(pEvent:TimerEvent):void 
		{
			if (_Moving)
			{
				var newPoint:Point;
				if (_Distraction)
				{
					newPoint = GetPoint(_AnimateTimer.currentCount + Utilities.RandRange(0, 10), _AnimateTimer.repeatCount);
				}
				else
				{
					newPoint = GetPoint(_AnimateTimer.currentCount, _AnimateTimer.repeatCount);
				}
				this.x = newPoint.x;
				this.y = newPoint.y;
			}
			if (_Spinning)
			{
				this.rotation = (this.rotation - Turns.DistractionArrowSpinSpeed) % 360;
			}
		}
		
		private function InitAnimateTimer(pMillisecondsPerBeat:Number):void
		{
			_AnimateTimer = new Timer(_TimerInterval, pMillisecondsPerBeat / _TimerInterval);
			_AnimateTimer.addEventListener(TimerEvent.TIMER, OnAnimateTimer);
		}
	}
}