package com.learningrx
{
	import flash.display.DisplayObject;
	import flash.display.DisplayObjectContainer;
	import flash.display.Sprite;
	import flash.filters.*;
	import flash.geom.Point;
	import flash.geom.ColorTransform;
	import flash.text.TextFormat;
	import flash.text.TextField;
	import flash.text.TextFieldAutoSize;
	import flash.text.AntiAliasType;
	import flash.utils.Timer;
	import flash.utils.ByteArray;
	import flash.events.TimerEvent;

	public class Utilities
	{
		private static var _PauseTimerCompleteFunction:Function;
		private static var _PauseTimer:Timer;
		
		public static function PauseTimer(pSeconds:Number,
													 pCompleteFunction:Function):void
		{
			_PauseTimerCompleteFunction = pCompleteFunction;
			_PauseTimer = new Timer(100, pSeconds * 10);
			_PauseTimer.addEventListener(TimerEvent.TIMER_COMPLETE, PauseTimerComplete);
         _PauseTimer.start();
		}

		private static function PauseTimerComplete(pEvent:TimerEvent):void
		{
         _PauseTimer = null;
			_PauseTimerCompleteFunction();
		}

		public static function RandRange(pStart:Number, 
		                                 pEnd:Number):Number
		{
			var tAnswer:Number = Math.round(pStart + (Math.random() * (pEnd - pStart)));
			//trace('RandRange', pStart, pEnd, tAnswer);
			return tAnswer;
		}

		public static function GetCircularArrayValue(pArray:Array, 
																	pValue:Number):Number
		{
			var tAnswer:Number = pArray[(pValue) % pArray.length];
			//trace('GetCircularArrayValue', pArray, pValue, tAnswer);
			return tAnswer;
		}

	   public static function RemoveElementFromArray(pArray:Array, pElement:*):void
		{
			var index:Number = GetFirstOccurenceInArray(pArray, pElement);
			pArray.splice(index, 1);
		}
	  
		public static function GetFirstOccurenceInArray(pArray:Array, 
																		pElement:*):Number
		{
			for (var i:Number = 0; i < pArray.length; ++i)
			{
				if (pArray[i] == pElement)
				{
					return i;
				}
			}
			return NaN;
	  }
	  
		public static function ObjectLength(pObject:Object):Number
		{
			var length:Number = 0;
			for each (var item:* in pObject)
			{
				++length;;
			}
			return length;
		}

		public static function Distance(pPoint1:Object, 
												  pPoint2:Object)
		{
			var xDist:Number = Math.round(pPoint1.x - pPoint2.x); 
			var yDist:Number = Math.round(pPoint1.y - pPoint2.y); 
			return Math.round(Math.sqrt((xDist * xDist) + (yDist *yDist))); 
		}

		public static function GetRandomValueFromArray(pArray:Array):*
		{
			var index:Number = RandRange(0, pArray.length - 1);
			//trace('GetRandomValueFromArray', pArray, index);
			return pArray[index];
		}
		
		public static function GetUniqueRandomValueFromArray(pArray:Array, 
																			  pValuesToExclude:Array):*
		{
			if (pValuesToExclude.length > pArray.length)
			{
				return null;
			}
			var value:*;
			do
			{
				value = GetRandomValueFromArray(pArray);
			}
			while (ArrayContains(pValuesToExclude, value));
			return value;
		}

		public static function ArrayContains(pArray:Array, 
		                                     pElement:*):Boolean
		{
			for (var i:Number = 0; i < pArray.length; ++i)
			{
				if (pArray[i] == pElement)
				{
					return true;
				}
			}
			return false
	  }
	  
	  public static function ColorDisplayObject(pDisplayObject:DisplayObject,
	                                            pRGB:Number):void
	  {
			var color:ColorTransform = pDisplayObject.transform.colorTransform;
			color.color = pRGB;
			pDisplayObject.transform.colorTransform = color;
	  }
	  
	  public static function TraceObject(pObject:Object):void
	  {
			if (typeof(pObject) == "object")
			{
				for (var prop in pObject) 
				{ 
					trace(prop + ":"); 
					TraceObject(pObject[prop]);
				}
			}
			else
			{
				trace(pObject.toString());
			}
		}

		public static function Capitalize(pString:String, pCapAllWords:Boolean):String
		{
			if (pCapAllWords === true)
			{ 
				return pString.replace(/^.|\b./g, _upperCase);
			}
			else
			{
				return pString.replace(/(^\w)/, _upperCase);
			}
		}

		private static function _upperCase(pChar:String, ...args):String 
		{
			return pChar.toUpperCase();
		}
		
		public static function RemoveSpaces(pString:String):String
		{
			var array:Array = pString.split(' ');
			return array.join("");	
		}

		public static function GetGlobalToLocal(pDisplayObject:DisplayObject, pX:Number, pY:Number):Point
		{
			var point1:Point = new Point(pX, pY);
			return pDisplayObject.localToGlobal(point1);
		}

		public static function GetLocalToGlobal(pDisplayObject:DisplayObject, pX:Number, pY:Number):Point
		{
			var point1:Point = new Point(pX, pY);
			return pDisplayObject.globalToLocal(point1);
		}

		public static function MoveChildToTopOfDisplayList(pDisplayObject:DisplayObjectContainer,
																		   pChild:DisplayObject):void
		{
			if (pChild != null)
			{
				if (pDisplayObject.contains(pChild))
				{
					pDisplayObject.setChildIndex(pChild, pDisplayObject.numChildren - 1);
				}
			}
		}
		
		public static function MoveChildToBottomOfDisplayList(pDisplayObject:DisplayObjectContainer,
																				pChild:DisplayObject):void
		{
			if (pChild != null)
			{
				if (pDisplayObject.contains(pChild))
				{
					pDisplayObject.setChildIndex(pChild, 0);
				}
			}
		}
		
		public static function AddChildToDisplayList(pDisplayObject:DisplayObjectContainer, 
																	pChild:DisplayObject,
																	pIdentifier:String = ''):Boolean
		{
			if (!pDisplayObject.contains(pChild))
			{
				pDisplayObject.addChild(pChild);
			}
		}

		public static function RemoveChildFromDisplayList(pDisplayObject:DisplayObjectContainer, 
																		  pChild):Boolean
		{
			if (pChild != null)
			{
				if (pDisplayObject.contains(pChild))
				{
					pDisplayObject.removeChild(pChild);
				}
			}
		}
		
		public static function RemoveLastChildFromDisplayList(pDisplayObject:DisplayObjectContainer):void
		{
			if (pDisplayObject.numChildren > 0)
			{
				pDisplayObject.removeChildAt(pDisplayObject.numChildren - 1);
			}
		}
		
		public static function RemoveAllChildrenFromDisplayList(pDisplayObject:DisplayObjectContainer):void
		{
			while (pDisplayObject.numChildren > 0)
			{
				pDisplayObject.removeChildAt(0);
			}
		}
		
		public static function Between(pValue:Number, 
												 pMinimum:Number, 
												 pMaximum:Number):Number
		{
			return Math.max(pMinimum, Math.min(pMaximum, pValue));
		}
		
		public static function CloneObject(pSource:Object):Object 
		{
			var copier:ByteArray = new ByteArray();
			copier.writeObject(pSource);
			copier.position = 0;
			return(copier.readObject());
		}

		public static function ResetTimer(pTimer:Timer):void
		{
         if (pTimer != null)
			{
				pTimer.reset();
			}
		}

		public static function StopTimer(pTimer:Timer):void
		{
         if (pTimer != null)
			{
				pTimer.reset();
			}
		}

		public static function StartTimer(pTimer:Timer):void
		{
         if (pTimer != null)
			{
				pTimer.start();
			}
		}

		public static function RestartTimer(pTimer:Timer):void
		{
         if (pTimer != null)
			{
				pTimer.reset();
				pTimer.start();
			}
		}

		public function GetTimeFromDateString(vDateString:String):Object
		{
			var date:Object = new Object();
			date.year = Number(vDateString.substr(0, 4));
			date.month = Number(vDateString.substr(5, 2));
			date.day = Number(vDateString.substr(8, 2));
			return date;
		}

		public static function GetTimeFromTimeString(pTimeString:String):Object
		{
			var time:Object = new Object();
			time.hour = Number(pTimeString.substr(0, 2));
			time.minute = Number(pTimeString.substr(3, 2));
			time.second = Number(pTimeString.substr(6, 2));
			return time;
		}

		public static function FormatDateForMySQL(pDay:Number, 
																pMonth:Number, 
																pYear:Number):String
		{
			var day:String = "";
			if (pDay < 0)
			{
				day = "0" + pDay;
			} 
			else
			{
				day = pDay.toString();
			}
			var month:String = "";
			if (pMonth < 0)
			{
				month = "0" + pMonth;
			} 
			else
			{
				month = pMonth.toString();
			}
			var tDateString:String = pYear.toString() + ":" + month + ":" + day;
			return tDateString;
		}
		
		public static function get ObjectBevel():BevelFilter
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
			return bevelFilter;
		}

		public static function get LineBevel():BevelFilter
		{
			var bevelFilter:BevelFilter = new BevelFilter();
			bevelFilter.distance = 1;
			bevelFilter.angle = 295;
			bevelFilter.highlightColor = 0xFFFFFF;
			bevelFilter.highlightAlpha = 1;
			bevelFilter.shadowColor = 0x000033;
			bevelFilter.shadowAlpha = 1;
			bevelFilter.blurX = 2;
			bevelFilter.blurY = 2;
			bevelFilter.strength = 1;
			bevelFilter.quality = BitmapFilterQuality.HIGH;
			bevelFilter.type = BitmapFilterType.OUTER;
			bevelFilter.knockout = false;
			return bevelFilter;
		}
		
		public static function get ObjectDropShadow():DropShadowFilter
		{
			var dropShadowFilter:DropShadowFilter = new DropShadowFilter();
			dropShadowFilter.distance = 5;
			dropShadowFilter.color = 0x000000;
			dropShadowFilter.angle = 45;
			dropShadowFilter.alpha = .5;
			dropShadowFilter.blurX = 5;
			dropShadowFilter.blurY = 5;
			dropShadowFilter.quality = BitmapFilterQuality.HIGH;
			dropShadowFilter.knockout = false;
			return dropShadowFilter;
		}
		
		public static function get ScreenDropShadow():DropShadowFilter
		{
			var dropShadowFilter:DropShadowFilter = new DropShadowFilter();
			dropShadowFilter.angle = 39;
			dropShadowFilter.alpha = 80;
			dropShadowFilter.blurX = 30;
			dropShadowFilter.blurY = 30;
			dropShadowFilter.quality = 3;
			return dropShadowFilter;
		}



		public static function FormatTextField(pTextField:TextField,
															pFontSize:Number,
															pAutoSize:Boolean = true,
															pFontName:String = 'Arial'):void
		{
			pTextField.antiAliasType = flash.text.AntiAliasType.ADVANCED;
			pTextField.embedFonts = true;
			if (pAutoSize)
			{
				pTextField.autoSize = TextFieldAutoSize.LEFT
			}
			var format:TextFormat = new TextFormat();
			format.font = pFontName;
			format.color = 0xFFFFFF;
			format.size = pFontSize;
			pTextField.defaultTextFormat = format;
		}
	}
}