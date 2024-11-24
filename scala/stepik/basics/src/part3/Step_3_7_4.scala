package part3

object Step_3_7_4 {
  sealed trait AccountType
  case object FreeAccount extends AccountType
  case object PaidAccount extends AccountType

  sealed trait SubscriptionStatus
  case object Subscribed extends SubscriptionStatus
  case object Unsubscribed extends SubscriptionStatus
  case object SubscriptionMissingData extends SubscriptionStatus

  object Settings {
    case class AccountSettings(email: String, password: String, picture: String)
    case class SubscriptionSettings(
        paymentMethod: String,
        notifications: String,
        expiration: String
    )
  }

  object Unsubscriber {
    def unsubscribe(accountId: Int): Unit = println(s"$accountId unsubscribed")
  }

  abstract class Account(
      accountId: Int,
      accountType: AccountType,
      settings: Settings.AccountSettings
  ) {
    def info(): Unit = println(s"Account Type: $accountType")
    def subscribe(accountId: Int): Unit = println(s"$accountId ${settings.email} subscribed")
    def performAction(): Unit
  }

  case class BaseAccount(
      accountId: Int,
      settings: Settings.AccountSettings
  ) extends Account(accountId, FreeAccount, settings) {
    val accountType = FreeAccount

    override def performAction(): Unit = {
      subscribe(this.accountId)
    }
    override def toString(): String = s"BaseAccount($accountId,FreeAccount,$settings)"
  }

  object BaseAccount {
    def apply(
        accountId: Int,
        accountType: AccountType,
        settings: Settings.AccountSettings
    ): BaseAccount = BaseAccount(accountId, settings)
  }

  case class PrivilegedAccount(
      accountId: Int,
      accountType: AccountType,
      settings: Settings.AccountSettings,
      subscriptionStatus: SubscriptionStatus
  ) extends Account(accountId, accountType, settings) {
    override def performAction(): Unit = {
      Unsubscriber.unsubscribe(this.accountId)
    }
    override def info(): Unit = {
      super.info()
      println(s"Subscription Status: $subscriptionStatus")
    }
  }

  def main(args: Array[String]): Unit = {
    val baseAccount = BaseAccount(
      accountId = 1,
      accountType = PaidAccount,
      settings = Settings.AccountSettings(
        email = "test@mail.com",
        password = "abr#45&",
        picture = "link/to/some/pic"
      )
    )

    baseAccount.info()
    println(baseAccount)
    baseAccount.performAction()
  }
}
