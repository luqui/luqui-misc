package com.learningrx.ComprehensionFigures
{
	import flash.display.SimpleButton; 
	import flash.filters.DropShadowFilter;
	import flash.events.MouseEvent;
	import flash.text.TextField;
	import flash.utils.Timer;
	import flash.events.TimerEvent;
	
	import com.learningrx.*;
	import com.learningrx.Screens.*;

	
	public class KeyBox extends Screen
	{
		private const KEY_FADE_SECONDS:Number = .3;
		private const KEY_FADE_OUT:String = "out";
		private const KEY_FADE_IN:String = "in";
		private const KEY_TIMER_INTERVAL:Number = 10; // lower means smoother fade

		private var _Key:Array;
		private var _KeyLabel:TextField;
		private var _KeyFadeTimer:Timer;
		private var _KeyFadeSeconds:Number = KEY_FADE_SECONDS;
		private var _KeyFadeDirection:String = KEY_FADE_OUT;
		private var _Children:Array = new Array();
		private var _MaximizedY:Number;
		private var _MinimizedY:Number;
		
		public function KeyBox(pParent:Game,
									  pMaximizedY:Number)
		{
			super(pParent);
			CreateBackground();
			CreateKeyLabel();
			_MaximizedY = pMaximizedY;
			_MinimizedY = Math.round(pMaximizedY - this.height);
		}

		public function RemoveAllChildrenFromDisplayList():void
		{
			if (_Children.length > 0)
			{
				for (var i:Number = 0; i < _Children.length; ++ i)
				{
					Utilities.RemoveChildFromDisplayList(this, _Children[i]);
				}
				_Children = new Array();
			}
		}

		protected function CreateBackground():void
		{
			this.graphics.beginFill(0x666666, .3)
			this.graphics.lineStyle(0, 0x666666, 0, true, "none", "none", "round");
			this.graphics.drawRect(0, 0, 888, 65);
			this.graphics.endFill(); 
			var dividingLine = new DividingLine(888);
			Utilities.AddChildToDisplayList(this, dividingLine);
			dividingLine.y = 64;
			dividingLine.x = -1;
		}
			
		protected function CreateKeyLabel():void
		{
			_KeyLabel = new TextField();
			Utilities.FormatTextField(_KeyLabel, 20);
			_KeyLabel.text = 'KEY:';
			_KeyLabel.height = 20;
			_KeyLabel.selectable = false;
			_KeyLabel.x = 6;
			_KeyLabel.y = 20;
			Utilities.AddChildToDisplayList(this, _KeyLabel);
		}
			
		protected function InitKeyFadeTimer(pSeconds:Number,
														pDirection:String):void
		{
			_KeyFadeSeconds = pSeconds;
			_KeyFadeDirection = pDirection;
			_KeyFadeTimer = new Timer(KEY_TIMER_INTERVAL, _KeyFadeSeconds * 1000 / KEY_TIMER_INTERVAL);
			_KeyFadeTimer.addEventListener(TimerEvent.TIMER, OnKeyFadeTimer);
			_KeyFadeTimer.addEventListener(TimerEvent.TIMER_COMPLETE, OnKeyFadeTimerComplete);
			if (KEY_FADE_IN == _KeyFadeDirection)
			{
				this.y = _MinimizedY;
			}
			else
			{
				this.y = _MaximizedY;
			}
		}

		protected function StartKeyFadeTimer():void
		{
         _KeyFadeTimer.start();
		}

		protected function OnKeyFadeTimerComplete(pEvent:TimerEvent):void 
		{
         _KeyFadeTimer.reset();
			if (KEY_FADE_IN == _KeyFadeDirection)
			{
				Show();
			}
			else
			{
				Hide();
			}
		}
		
		protected function OnKeyFadeTimer(pEvent:TimerEvent):void
		{
			if (KEY_FADE_IN == _KeyFadeDirection)
			{
				this.y = _MinimizedY + (_MaximizedY -_MinimizedY) * (_KeyFadeTimer.currentCount / _KeyFadeTimer.repeatCount);
			}
			else
			{
				this.y = _MaximizedY - (_MaximizedY -_MinimizedY) * (_KeyFadeTimer.currentCount / _KeyFadeTimer.repeatCount);
			}
			_Parent.PositionAnswerBoxes();
		}

		public function Hide():void
		{
			this.y = _MinimizedY;
		}

		public function Show():void
		{
			this.y = _MaximizedY;
		}

		public function FadeKeyOut():void
		{
			if (this.y > _MinimizedY)
			{
				InitKeyFadeTimer(KEY_FADE_SECONDS, KEY_FADE_OUT);
				StartKeyFadeTimer();
			}
		}

		public function FadeKeyIn():void
		{
         if (this.y < _MaximizedY)
			{
				InitKeyFadeTimer(KEY_FADE_SECONDS, KEY_FADE_IN);
				StartKeyFadeTimer();
			}
		}

		public function AddChildToDisplayList(pChild:*):void
		{
			Utilities.AddChildToDisplayList(this, pChild);
			_Children.push(pChild);
		}
		
		public function InitKey(pKey:Array):void
		{
			RemoveAllChildrenFromDisplayList();
			_Key = pKey;
			if (_Key.length == 0)
			{
				return; // Scram if _Key hasn't been created yet.
			}
			var codeItems:Array = new Array();
			var totalItemWidths:Number = 0;
			var spaceBetweenShapeAndText:Number = 5;
			for (var i:Number = 0; i < _Key.length; ++ i)
			{
				codeItems[i] = new Object();
				codeItems[i].CFShape = new CFShape(_Key[i].Shape.Name);
				codeItems[i].CFShape.HideFill();
				codeItems[i].CFShape.width = codeItems[i].CFShape.height = 40;
				AddChildToDisplayList(codeItems[i].CFShape);
				codeItems[i].CFTextField = new TextField;
				codeItems[i].CFTextField.width = 200;
				Utilities.FormatTextField(codeItems[i].CFTextField, 18);
				AddChildToDisplayList(codeItems[i].CFTextField);
				codeItems[i].CFTextField.text = '= ' + _Key[i].Name;
				totalItemWidths += codeItems[i].CFShape.width + spaceBetweenShapeAndText + codeItems[i].CFTextField.textWidth;
			}
			var spaceBetweenItems:Number = (this.width - (_KeyLabel.x + _KeyLabel.textWidth) - totalItemWidths) / (_Key.length + 1);
			codeItems[0].CFShape.y = _KeyLabel.y + (_KeyLabel.textHeight - codeItems[0].CFShape.height) / 2;
			codeItems[0].CFShape.x = _KeyLabel.x + _KeyLabel.textWidth + spaceBetweenItems;
			codeItems[0].CFTextField.y = codeItems[0].CFShape.y + 
												  (codeItems[0].CFShape.height - codeItems[0].CFTextField.textHeight) / 2;
			codeItems[0].CFTextField.x = codeItems[0].CFShape.x + codeItems[0].CFShape.width + spaceBetweenShapeAndText;
			for (i = 1; i < _Key.length; ++ i)
			{
				codeItems[i].CFShape.y = codeItems[0].CFShape.y;
				codeItems[i].CFShape.x = codeItems[i - 1].CFTextField.x + codeItems[i - 1].CFTextField.textWidth + spaceBetweenItems;
				codeItems[i].CFTextField.y = codeItems[0].CFTextField.y;
				codeItems[i].CFTextField.x = codeItems[i].CFShape.x + codeItems[i].CFShape.width + spaceBetweenShapeAndText;
			}
		}
		
	}
}